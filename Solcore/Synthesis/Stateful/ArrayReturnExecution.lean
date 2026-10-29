import Solcore.Synthesis.Core.ArrayReturn
import Solcore.Synthesis.Stateful.StorageExecution
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute the original checked array-return contract over a persistent account
world. Each invocation starts a fresh Core heap and only the public terminal
`finalWorld` becomes the next transaction's world. Calldata is the selector of
`run(uint256,uint256,uint256,uint256)` with the flags, input, choice and length
Words. Observations report the whole return data, the three declared slots and
the contract's whole committed storage.

`model` is an independent reading of the emitted source: a slot map, the step
evaluated alone in Core, the count and inner lengths read from the
transaction's `length` and `choice`, the elements' memory as the method writes
it, and std's `abi_encode` of the memory array run over a byte buffer: the
array encoder's offset, length and element loop, each element's codec, and for
`bytes` elements `encodeIntoFromBytesLike`, which copies the length Word and
the data from the element's memory and zeroes the rest of the last Word. A
reverted transaction keeps the prior slots. It shares nothing with the Core
contract but that step. Tests compare the two; neither is an oracle for the
differential paths. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.ArrayReturnExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ArrayReturn (CheckedPlan Element Shape)

def historySchema : String := "solcore-lean.array-return-history.v1"

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
def observedSlots : List Word := (List.range ArrayReturn.slotCount).map Word.ofNatModulo

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
array, or the one reverted Word) and the slots it leaves committed. -/
structure ModelRow where
  reverted : Bool
  output : ByteArray
  slots : List Word

private def slotAt (slots : List Word) (slot : Nat) : Word := slots.getD slot Word.zero

/-- An element's memory as the method writes it: a Word (`uint256`, or
`bytes4` right-aligned), a `bytes` value's 96 bytes (its length Word and two
data Words, dirty past the length), or an inner array's Words. -/
inductive Value where
  | word (value : Word)
  | block (length : Nat) (memory : ByteArray)
  | inner (values : List Word)

/-- A byte buffer standing for EVM memory: writes past the end extend it with
zeros, as memory expansion does. -/
private def write (buffer : ByteArray) (offset : Nat) (bytes : ByteArray) : ByteArray :=
  let padded := if buffer.size < offset + bytes.size then
      buffer ++ ⟨Array.replicate (offset + bytes.size - buffer.size) 0⟩
    else buffer
  bytes.copySlice 0 padded offset bytes.size

private def mstore (buffer : ByteArray) (offset : Nat) (value : Word) : ByteArray :=
  write buffer offset (encodeWordBytesBE value)

private def wordAt (value : Nat) : Word := Word.ofNatModulo value

/-- `encodeInto` of one element at `base + offset` with the tail at `tail`, as
std's codecs do; returns the buffer and the new tail. `uint256` stores its
Word, `bytes4` its Word shifted left by 224, `bytes` its offset from `base`,
then `length + 32` bytes copied from its memory and zeros to a whole Word, and
an inner array its offset, its length and its Words. -/
private def encodeElement (buffer : ByteArray) (base offset tail : Nat) : Value → ByteArray × Nat
  | .word value => (mstore buffer (base + offset) value, tail)
  | .block length memory =>
      let total := length + 32
      let rounded := (total + 31) / 32 * 32
      let buffer := mstore buffer (base + offset) (wordAt (tail - base))
      let buffer := write buffer tail (memory.extract 0 total)
      (write buffer (tail + total) ⟨Array.replicate (rounded - total) 0⟩, tail + rounded)
  | .inner values =>
      let buffer := mstore buffer (base + offset) (wordAt (tail - base))
      let buffer := mstore buffer tail (wordAt values.length)
      let buffer := values.zipIdx.foldl (fun buffer (value, index) => mstore buffer (tail + 32 + 32 * index) value)
        buffer
      (buffer, tail + 32 + 32 * values.length)

/-- std's `abi_encode` of a `memory<DynArray<t>>`: the head's offset Word, then
`ABIEncode<memory<DynArray<t>>>.encodeInto`, which writes the length at the
tail and runs each element's codec at stride 32 into the element region, the
dynamic tails following the heads. -/
def stdEncoding (element : Element) (values : List Value) : ByteArray := Id.run do
  let start := 32
  let tail := start + 32
  let mut buffer := mstore ByteArray.empty start (wordAt (tail - start))
  buffer := mstore buffer tail (wordAt values.length)
  let elements := tail + 32
  let mut next := elements + 32 * values.length
  for (value, index) in values.zipIdx do
    let shifted := match element, value with
      | .fourBytes, .word word => Value.word (word * wordAt (2 ^ 224))
      | _, value => value
    let (written, newTail) := encodeElement buffer elements (32 * index) next shifted
    buffer := written
    next := newTail
  return buffer.extract start next

/-- It follows the source: `sc_count = length % 4`, `sc_prior = sload(0)`,
`sc_last = sload(2)`, `sc_result = sc_step(sc_prior + sc_input)`, the three
writes, then `sc_calls = sload(1)` and `sc_mix = (sc_calls * K) ^ sc_last`;
element `i` below the count holds `a = sc_result * K + i` and `b = sc_mix + i`:
the Word `a`, `bytes4(a & 0xffffffff)`, 96 bytes of the inner length
`(choice / 65^i) % 65`, `a` and `b`, or an inner array of the first
`(choice / 3^i) % 3` of `a` and `b`. -/
def modelTransaction (step : Aggregates.CheckedDAG) (fuel : Nat) (element : Element) (prior : List Word)
    (transaction : Transaction) : Option ModelRow := do
  let before := slotAt prior 0
  let last := slotAt prior 2
  let result ← stepResult step fuel (before + transaction.input)
  let written := ((prior.set 0 result).set 1 (slotAt prior 1 + Word.ofNatModulo 1)).set 2 transaction.input
  if transaction.flags.val % 2 == 1 then
    return ⟨true, encodeWordBytesBE result, prior⟩
  let multiplier := Word.ofNatModulo ArrayReturn.multiplier
  let mix := (slotAt written 1 * multiplier) ^^^ last
  let count := transaction.length.val % 4
  let values := (List.range count).map fun index =>
    let a := result * multiplier + wordAt index
    let b := mix + wordAt index
    match element with
    | .words => Value.word a
    | .fourBytes => Value.word (a.bitAnd (wordAt 0xffffffff))
    | .bytes =>
        let length := transaction.choice.val / 65 ^ index % 65
        Value.block length (encodeWordBytesBE (wordAt length) ++ encodeWordBytesBE a ++ encodeWordBytesBE b)
    | .nested => Value.inner ([a, b].take (transaction.choice.val / 3 ^ index % 3))
  return ⟨false, stdEncoding element values, written⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (fuel : Nat) (element : Element) (transactions : List Transaction) :
    Option (List ModelRow) := Id.run do
  let mut slots : List Word := List.replicate ArrayReturn.slotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step fuel element slots transaction with
    | some row =>
        rows := rows.push row
        slots := row.slots
    | none => return none
  return some rows.toList

end Solcore.Synthesis.Stateful.ArrayReturnExecution
