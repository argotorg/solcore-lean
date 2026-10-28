import Solcore.Synthesis.Core.StorageLoop
import Solcore.Synthesis.Stateful.StorageExecution
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute the original checked storage-loop contract over a persistent
account world. Each invocation starts a fresh Core heap and only the public
terminal `finalWorld` becomes the next transaction's world. Calldata is the
selector of `run(uint256,uint256)` with the flags and input Words.
Observations report the nine declared slots and the contract's whole committed
storage.

`model` is an independent reading of the emitted source: a counter runs a
while loop over a slot map, the slots are computed from the counter, and
reverted transactions keep the prior slots. It evaluates the step's Core alone
at each argument and shares nothing with the guarded contract but that step.
Tests compare the two; neither is an oracle for the differential paths. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.StorageLoopExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.StorageLoop (CheckedPlan)

def historySchema : String := "solcore-lean.storage-loop-history.v1"

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

/-- The iterations a transaction runs: its input's bits under the mask. -/
def iterations (mask : Nat) (input : Word) : Nat := (input.bitAnd (Word.ofNatModulo mask)).val

/-- Slot zero holds the accumulator, slot one the committed iteration total and
slot `2 + i` iteration `i`'s result. -/
def observedSlots : List Word := (List.range StorageLoop.slotCount).map Word.ofNatModulo

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
prior committed world through the public runtime, not through this observer. -/
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

/-- One modelled transaction: whether it reverts, its result Word and the slots
it leaves committed. The loop follows the source: `sc_limit = input & mask`,
a counter from zero while `sc_limit > sc_counter`, `sc_slot = sc_counter + 2`. -/
structure ModelRow where
  reverted : Bool
  result : Word
  slots : List Word
  deriving BEq

private def slotAt (slots : List Word) (slot : Nat) : Word := slots.getD slot Word.zero

def modelTransaction (step : Aggregates.CheckedDAG) (fuel mask : Nat) (prior : List Word)
    (transaction : Transaction) : Option ModelRow := Id.run do
  let limit := iterations mask transaction.input
  let mut slots := prior
  let mut counter := 0
  let mut failed := false
  -- At most the mask's iterations; the guard keeps the loop structural.
  for _ in List.range StorageLoop.maxIterations do
    if !failed && limit > counter then
      let slot := counter + 2
      let argument := slotAt slots 0 + slotAt slots 1 + slotAt slots (slot - 1) + slotAt slots slot + transaction.input
      match stepResult step fuel argument with
      | some value =>
          slots := (slots.set slot value).set 0 value
          counter := counter + 1
      | none => failed := true
  if failed then return none
  slots := slots.set 1 (slotAt slots 1 + Word.ofNatModulo limit)
  let result := slotAt slots 0 + slotAt slots 1
  let reverted := transaction.flags.val % 2 == 1
  return some ⟨reverted, result, if reverted then prior else slots⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (fuel mask : Nat) (transactions : List Transaction) :
    Option (List ModelRow) := Id.run do
  let mut slots : List Word := List.replicate StorageLoop.slotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step fuel mask slots transaction with
    | some row =>
        rows := rows.push row
        slots := row.slots
    | none => return none
  return some rows.toList

end Solcore.Synthesis.Stateful.StorageLoopExecution
