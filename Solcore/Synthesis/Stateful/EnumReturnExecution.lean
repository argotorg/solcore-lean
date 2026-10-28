import Solcore.Synthesis.Core.EnumReturn
import Solcore.Synthesis.Stateful.StorageExecution
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute the original checked enum-return contract over a persistent account
world. Each invocation starts a fresh Core heap and only the public terminal
`finalWorld` becomes the next transaction's world. Calldata is the selector of
`run(uint256,uint256,uint256,uint256)` with the flags, input, choice and length
Words. Observations report the whole return data, the three declared slots and
the contract's whole committed storage.

`model` is an independent reading of the emitted source and of std's encoder:
a slot map, the step evaluated alone in Core, the method's choice of
constructor and its 96 bytes of `bytes` data, then std's `abi_encode` of the
enum written out over a zeroed byte memory. The encoder is `encodeVariant` with
the head sizes of `ABIAttribs`, the unit, `uint256` and pair encoders and
`encodeIntoFromBytesLike`. A reverted transaction keeps the prior slots. It
shares nothing with the Core contract but that step and the tags. Tests compare
the two; neither is an oracle for the differential paths. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.EnumReturnExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumReturn (CheckedPlan Constructor Shape)

def historySchema : String := "solcore-lean.enum-return-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  input : Word
  choice : Word
  length : Word
  deriving BEq

/-- The selector of `run(uint256,uint256,uint256,uint256)`, then the flags,
input, choice and length Words. -/
def inputData (flags input choice length : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x15, 0x50, 0x9d, 0x2b] ++ encodeWordBytesBE flags ++ encodeWordBytesBE input ++
    encodeWordBytesBE choice ++ encodeWordBytesBE length
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags input choice length : Word) : String :=
  encodeBytesText (inputData flags input choice length).bytes

/-- Slot zero holds the accumulator, slot one the committed call count and slot
two the last committed input. -/
def observedSlots : List Word := (List.range EnumReturn.slotCount).map Word.ofNatModulo

def slotsJson : Json := toJson (observedSlots.map fun slot => toString slot.val)

def storageJson (account : Account) : Json := toJson (observedSlots.map fun slot => Json.mkObj [
  ("slot", toJson (toString slot.val)),
  ("value", toJson (toString (account.storageRead slot).val))])

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => storageJson account
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation. The code registry is resolved again
against each current committed world, so persistence cannot install a different
contract or retain one invocation's local heap. A reverted invocation keeps the
prior committed world through the public runtime, not through this observer.
The output is the decoded convention's whole return data. -/
def observeContract (contract : CheckedCoreContract) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := StorageExecution.initialWorldForContract contract bindings
  let initial := worldStorage world bindings
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match registry.resolve? prior bindings.address with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"), ("committedStorage", worldStorage prior bindings),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          let invocation : TopLevelInvocation := {
            target := bindings.address, caller := bindings.caller, callValue := Word.zero,
            inputData := inputData transaction.flags transaction.input transaction.choice transaction.length }
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedStorage", worldStorage world bindings),
                ("accountStorage", AccountStorage.contractJson world bindings.address)]))
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"), ("committedStorage", worldStorage prior bindings),
                ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", slotsJson),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

/-- The step's own Core result at one argument. -/
def stepResult (step : Aggregates.CheckedDAG) (fuel : Nat) (argument : Word) : Option Word :=
  match (step.instantiate argument).toCore.runStateful fuel with
  | .done (.word value) _ => some value
  | _ => none

/-- One modelled transaction: whether it reverts, its whole output (the encoded
returned value, or the one reverted Word) and the slots it leaves committed. -/
structure ModelRow where
  reverted : Bool
  output : ByteArray
  slots : List Word

private def slotAt (slots : List Word) (slot : Nat) : Word := slots.getD slot Word.zero

/-- The memory std's encoder writes, zeroed beforehand. -/
private def memorySize : Nat := 512

/-- `mstore`: one big-endian Word at `offset`. -/
private def store (memory : ByteArray) (offset : Nat) (value : Word) : ByteArray :=
  (encodeWordBytesBE value).copySlice 0 memory offset 32

/-- The fields' head size of `ABIAttribs`: unit 0, `uint256` 32, a pair the sum
of its two, and `memory<bytes>` one offset Word. -/
private def headSize : EnumPayload → Nat
  | .noWords => 0
  | .oneWord => 32
  | .twoWords => 32 + 32
  | .boundedBytes => 32

/-- The derived instance's `innerHead`: 32 plus the widest constructor's head. -/
private def innerHead (constructors : List Constructor) : Nat :=
  32 + constructors.foldl (fun widest constructor => max widest (headSize constructor.payload)) 0

/-- `encodeIntoFromBytesLike` of the method's 96 bytes at `source`: the offset
Word, `length + 32` bytes copied from the length Word on, then zeros up to a
multiple of 32. It returns the memory and the new tail. -/
private def encodeBytes (memory source : ByteArray) (basePtr offset tail : Nat) : ByteArray × Nat :=
  let length := (decodeWordBytesBE? (source.extract 0 32)).getD Word.zero |>.val
  let total := length + 32
  let rounded := (total + 31) / 32 * 32
  let written := store memory (basePtr + offset) (Word.ofNatModulo (tail - basePtr))
  let copied := source.copySlice 0 written tail total
  (ByteArray.mk (Array.replicate (rounded - total) 0) |>.copySlice 0 copied (tail + total) (rounded - total),
    tail + rounded)

/-- std's `abi_encode` of constructor `constructor` with the fields `first`,
`second` and the `bytes` source, from address 0: the derived `encodeVariant`
writes the tag inline for a static enum, or the offset to a body in the tail for
a dynamic one, then the fields' encoders run. The return data is the memory
from 0 to the final tail. -/
def stdEncoding (constructors : List Constructor) (constructor : Constructor)
    (first second : Word) (source : ByteArray) : ByteArray :=
  let static := constructors.all (·.payload != .boundedBytes)
  let inner := innerHead constructors
  -- `abi_encode`: the head starts at `start`, the tail after the enum's head,
  -- the whole body for a static enum and one offset Word otherwise.
  let start := 0
  let tail := start + if static then inner else 32
  let tag := EnumReturn.tag constructor
  let memory := ByteArray.mk (Array.replicate memorySize 0)
  -- `encodeVariant`: the tag at the head, or the offset to a new base in the
  -- tail that holds the tag; the fields follow the tag.
  let (memory, basePtr, offset, tail) :=
    if static then (store memory start tag, start, 32, tail)
    else (store (store memory start (Word.ofNatModulo (tail - start))) tail tag, tail, 32, tail + inner)
  let (memory, final) := match constructor.payload with
    | .noWords => (memory, tail)
    | .oneWord => (store memory (basePtr + offset) first, tail)
    | .twoWords => (store (store memory (basePtr + offset) first) (basePtr + offset + 32) second, tail)
    | .boundedBytes => encodeBytes memory source basePtr offset tail
  memory.extract 0 final

/-- It follows the source: `sc_choice = choice % n`, `sc_length = length % 65`,
`sc_prior = sload(0)`, `sc_last = sload(2)`, `sc_result = sc_step(sc_prior +
sc_input)`, the three writes, then `sc_first = sc_result * K` and `sc_second =
(sload(1) * K) ^ sc_last`, and the constructor `sc_choice` with its fields; a
`bytes` constructor's 96 bytes are `sc_length`, `sc_first` and `sc_second`. -/
def modelTransaction (step : Aggregates.CheckedDAG) (constructors : List Constructor) (fuel : Nat)
    (prior : List Word) (transaction : Transaction) : Option ModelRow := do
  let before := slotAt prior 0
  let last := slotAt prior 2
  let result ← stepResult step fuel (before + transaction.input)
  let written := ((prior.set 0 result).set 1 (slotAt prior 1 + Word.ofNatModulo 1)).set 2 transaction.input
  if transaction.flags.val % 2 == 1 then
    return ⟨true, encodeWordBytesBE result, prior⟩
  let constructor ← constructors[transaction.choice.val % constructors.length]?
  let multiplier := Word.ofNatModulo EnumReturn.multiplier
  let first := result * multiplier
  let second := (slotAt written 1 * multiplier) ^^^ last
  let source := encodeWordBytesBE (Word.ofNatModulo (transaction.length.val % 65)) ++
    encodeWordBytesBE first ++ encodeWordBytesBE second
  return ⟨false, stdEncoding constructors constructor first second source, written⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (constructors : List Constructor) (fuel : Nat)
    (transactions : List Transaction) : Option (List ModelRow) := Id.run do
  let mut slots : List Word := List.replicate EnumReturn.slotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step constructors fuel slots transaction with
    | some row =>
        rows := rows.push row
        slots := row.slots
    | none => return none
  return some rows.toList

end Solcore.Synthesis.Stateful.EnumReturnExecution
