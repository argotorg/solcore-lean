import Solcore.Synthesis.Core.BytesReturn
import Solcore.Synthesis.Stateful.StorageExecution
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute the original checked bytes-return contract over a persistent account
world. Each invocation starts a fresh Core heap and only the public terminal
`finalWorld` becomes the next transaction's world. Calldata is the selector of
`run(uint256,uint256,uint256)` with the flags, input and length Words.
Observations report the whole return data, the three declared slots and the
contract's whole committed storage.

`model` is an independent reading of the emitted source: a slot map, the step
evaluated alone in Core, the method's three memory Words and std's
`encodeIntoFromBytesLike`, which writes the offset, copies the length Word and
`length` data bytes and zeroes the rest of the last Word. A reverted
transaction keeps the prior slots. It shares nothing with the Core contract but
that step. Tests compare the two; neither is an oracle for the differential
paths. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.BytesReturnExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.BytesReturn (CheckedPlan)

def historySchema : String := "solcore-lean.bytes-return-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  input : Word
  length : Word
  deriving BEq

/-- The selector of `run(uint256,uint256,uint256)`, then the flags, input and
length Words. -/
def inputData (flags input length : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x24, 0xb9, 0x12, 0xe5] ++ encodeWordBytesBE flags ++ encodeWordBytesBE input ++
    encodeWordBytesBE length
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags input length : Word) : String := encodeBytesText (inputData flags input length).bytes

/-- Slot zero holds the accumulator, slot one the committed call count and slot
two the last committed input. -/
def observedSlots : List Word := (List.range BytesReturn.slotCount).map Word.ofNatModulo

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
            inputData := inputData transaction.flags transaction.input transaction.length }
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

/-- std's `encodeIntoFromBytesLike` for the one returned value at `memory`: the
head offset 32, then `length + 32` bytes copied from the length Word on, then
zeros up to a multiple of 32. -/
def stdEncoding (memory : ByteArray) (length : Nat) : ByteArray :=
  let total := length + 32
  let rounded := (total + 31) / 32 * 32
  encodeWordBytesBE (Word.ofNatModulo 32) ++ memory.extract 0 total ++ ⟨Array.replicate (rounded - total) 0⟩

/-- It follows the source: `sc_length = length % 65`, `sc_prior = sload(0)`,
`sc_last = sload(2)`, `sc_result = sc_step(sc_prior + sc_input)`, the three
writes, then the 96 bytes at `sc_pointer`: `sc_length`, `sc_result * K` and
`(sload(1) * K) ^ sc_last`. -/
def modelTransaction (step : Aggregates.CheckedDAG) (fuel : Nat) (prior : List Word)
    (transaction : Transaction) : Option ModelRow := do
  let before := slotAt prior 0
  let last := slotAt prior 2
  let result ← stepResult step fuel (before + transaction.input)
  let written := ((prior.set 0 result).set 1 (slotAt prior 1 + Word.ofNatModulo 1)).set 2 transaction.input
  if transaction.flags.val % 2 == 1 then
    return ⟨true, encodeWordBytesBE result, prior⟩
  let length := transaction.length.val % 65
  let multiplier := Word.ofNatModulo BytesReturn.multiplier
  let memory := encodeWordBytesBE (Word.ofNatModulo length) ++ encodeWordBytesBE (result * multiplier) ++
    encodeWordBytesBE ((slotAt written 1 * multiplier) ^^^ last)
  return ⟨false, stdEncoding memory length, written⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (fuel : Nat) (transactions : List Transaction) :
    Option (List ModelRow) := Id.run do
  let mut slots : List Word := List.replicate BytesReturn.slotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step fuel slots transaction with
    | some row =>
        rows := rows.push row
        slots := row.slots
    | none => return none
  return some rows.toList

end Solcore.Synthesis.Stateful.BytesReturnExecution
