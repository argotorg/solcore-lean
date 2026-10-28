import Solcore.Synthesis.Core.TupleReturn
import Solcore.Synthesis.Stateful.StorageExecution
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute the original checked tuple-return contract over a persistent account
world. Each invocation starts a fresh Core heap and only the public terminal
`finalWorld` becomes the next transaction's world. Calldata is the selector of
`run(uint256,uint256)` with the flags and input Words. Observations report the
whole return data, the three declared slots and the contract's whole committed
storage.

`model` is an independent reading of the emitted source: a slot map, the step
evaluated alone in Core, and the returned Words listed in source order. A
reverted transaction keeps the prior slots. It shares nothing with the Core
contract but that step. Tests compare the two; neither is an oracle for the
differential paths. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.TupleReturnExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.TupleReturn (CheckedPlan)

def historySchema : String := "solcore-lean.tuple-return-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  input : Word
  deriving BEq

/-- The selector of `run(uint256,uint256)`, then the flags and input Words. -/
def inputData (flags input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x73, 0x57, 0xf5, 0xd2] ++ encodeWordBytesBE flags ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags input : Word) : String := encodeBytesText (inputData flags input).bytes

/-- Slot zero holds the accumulator, slot one the committed call count and slot
two the last committed input. -/
def observedSlots : List Word := (List.range TupleReturn.slotCount).map Word.ofNatModulo

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
            target := bindings.address, caller := bindings.caller,
            callValue := Word.zero, inputData := inputData transaction.flags transaction.input }
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

/-- One modelled transaction: whether it reverts, the Words of its output (the
returned tuple, or the one reverted Word) and the slots it leaves committed. It
follows the source: `sc_prior = sload(0)`, `sc_last = sload(2)`,
`sc_result = sc_step(sc_prior + sc_input)`, the three writes, then the returned
tuple `(sc_result, sload(1), sc_prior, sc_last)` cut to the arity. -/
structure ModelRow where
  reverted : Bool
  output : List Word
  slots : List Word
  deriving BEq

private def slotAt (slots : List Word) (slot : Nat) : Word := slots.getD slot Word.zero

def modelTransaction (step : Aggregates.CheckedDAG) (fuel arity : Nat) (prior : List Word)
    (transaction : Transaction) : Option ModelRow := do
  let before := slotAt prior 0
  let last := slotAt prior 2
  let result ← stepResult step fuel (before + transaction.input)
  let written := ((prior.set 0 result).set 1 (slotAt prior 1 + Word.ofNatModulo 1)).set 2 transaction.input
  let reverted := transaction.flags.val % 2 == 1
  let returned := [result, slotAt written 1, before, last].take arity
  return ⟨reverted, if reverted then [result] else returned, if reverted then prior else written⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (fuel arity : Nat) (transactions : List Transaction) :
    Option (List ModelRow) := Id.run do
  let mut slots : List Word := List.replicate TupleReturn.slotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step fuel arity slots transaction with
    | some row =>
        rows := rows.push row
        slots := row.slots
    | none => return none
  return some rows.toList

/-- The output bytes of a modelled row: its Words, big-endian and concatenated. -/
def outputBytes (row : ModelRow) : ByteArray :=
  row.output.foldl (fun bytes value => bytes ++ encodeWordBytesBE value) ByteArray.empty

end Solcore.Synthesis.Stateful.TupleReturnExecution
