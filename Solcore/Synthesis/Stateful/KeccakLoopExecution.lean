import Solcore.Synthesis.Core.KeccakLoop
import Solcore.Synthesis.Stateful.StorageMappingExecution
import Solcore.Synthesis.Stateful.EventLogExecution

/-! Execute the original checked Keccak-loop contract over a persistent account
world. Each invocation starts a fresh Core heap and an empty journal; only the
public terminal `finalWorld` becomes the next transaction's world, and only its
committed journal is reported, decoded under the event-log framing. The
observed slots are slot zero and the entry slot of every key the scenario's
transactions address, derived with the separate `Solcore.Abi.V1.Keccak256`
rather than the Core builders the contract runs.

`model` is an independent reading of the emitted source: a counter runs a
while loop over a slot map, each key's slot is hashed with that separate
Keccak, every iteration appends one log, and a reverted transaction keeps the
prior slots and commits no log. It evaluates the step's Core alone at each
argument and shares nothing with the guarded contract but that step. Tests
compare the two; neither is an oracle for the differential paths. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.KeccakLoopExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.KeccakLoop (CheckedPlan)

def historySchema : String := "solcore-lean.keccak-loop-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  input : Word
  deriving BEq

/-- The selector of `run(uint256,uint256)`, then the flags and input Words. -/
abbrev inputData := EventLogExecution.inputData

def calldata (flags input : Word) : String := encodeBytesText (inputData flags input).bytes

/-- The iterations a transaction runs: its input's bits under the loop mask. -/
def iterations (mask : Nat) (input : Word) : Nat := (input.bitAnd (Word.ofNatModulo mask)).val

/-- The key of iteration `ordinal`: the input's high bits and the ordinal's bits
under the key mask. -/
def key (keyMask : Nat) (input : Word) (ordinal : Nat) : Word :=
  (input.bitAnd (Word.ofNatModulo KeccakLoop.highMask)).bitOr (Word.ofNatModulo (ordinal &&& keyMask))

/-- The keys a transaction's iterations use, in iteration order. -/
def keys (mask keyMask : Nat) (input : Word) : List Word :=
  (List.range (iterations mask input)).map (key keyMask input)

/-- The pinned std's slot of `entries[key]`, from the independent ABI Keccak. -/
abbrev entrySlot := StorageMappingExecution.entrySlot

private def insertSlot (slot : Word) : List Word → List Word
  | [] => [slot]
  | head :: tail =>
      if slot.val < head.val then slot :: head :: tail
      else if slot.val = head.val then head :: tail
      else head :: insertSlot slot tail

/-- Slot zero and every addressed entry slot, in increasing numeric order
without duplicates: the protocol's complete write set. -/
def observedSlots (mask keyMask : Nat) (transactions : List Transaction) : List Word :=
  (transactions.flatMap fun tx => (keys mask keyMask tx.input).map entrySlot).foldl
    (fun slots slot => insertSlot slot slots) [Word.ofNatModulo KeccakLoop.accumulatorSlot]

private def worldStorage (world : WorldState) (bindings : Bindings) (slots : List Word) : Json :=
  match world.account? bindings.address with
  | some account => KeyedStorageExecution.storageJson account slots
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation. The code registry is resolved again
against each current committed world, so persistence cannot install a different
contract or retain one invocation's local heap or journal. -/
def observeContract (contract : CheckedCoreContract) (slots : List Word) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := StorageExecution.initialWorldForContract contract bindings
  let initial := worldStorage world bindings slots
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let invocation : TopLevelInvocation := {
        target := bindings.address, caller := bindings.caller,
        callValue := Word.zero, inputData := inputData transaction.flags transaction.input }
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match registry.resolve? prior bindings.address with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"), ("committedStorage", worldStorage prior bindings slots),
            ("accountStorage", AccountStorage.contractJson prior bindings.address), ("logs", Json.null)]))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              match EventLogExecution.decodeJournal terminal.committedJournal.logList with
              | .ok events =>
                  rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                    ("committedStorage", worldStorage world bindings slots),
                    ("accountStorage", AccountStorage.contractJson world bindings.address),
                    ("logs", EventLogExecution.eventsJson events)]))
                  match terminal.outcome with
                  | .trapped _ => stopped := some transaction.id
                  | _ => pure ()
              | .error error =>
                  rows := rows.push (Json.mkObj (common ++ [
                    ("status", toJson "observer-error"), ("detail", toJson error),
                    ("committedStorage", worldStorage world bindings slots),
                    ("accountStorage", AccountStorage.contractJson world bindings.address), ("logs", Json.null)]))
                  stopped := some transaction.id
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"), ("committedStorage", worldStorage prior bindings slots),
                ("accountStorage", AccountStorage.contractJson prior bindings.address), ("logs", Json.null)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", KeyedStorageExecution.slotsJson slots),
    ("framing", toJson Solcore.Synthesis.Core.EventLog.framingVersion),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("initialLogs", toJson ([] : List Json)),
    ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings slots),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract (observedSlots plan.mask plan.keyMask transactions) transactions bindings fuel

/-- The step's own Core result at one argument. -/
def stepResult (step : Aggregates.CheckedDAG) (fuel : Nat) (argument : Word) : Option Word :=
  match (step.instantiate argument).toCore.runStateful fuel with
  | .done (.word value) _ => some value
  | _ => none

/-- One modelled log: the ordinal and key topics and the written value. -/
structure ModelLog where
  ordinal : Nat
  key : Word
  value : Word
  deriving BEq

/-- One modelled transaction: whether it reverts, its result Word, the slots it
leaves committed as `(slot, value)` pairs and the logs it commits. -/
structure ModelRow where
  reverted : Bool
  result : Word
  storage : List (Word × Word)
  logs : List ModelLog
  deriving BEq

private def lookup (storage : List (Word × Word)) (slot : Word) : Word :=
  ((storage.find? fun (candidate, _) => candidate == slot).map Prod.snd).getD Word.zero

private def update (storage : List (Word × Word)) (slot value : Word) : List (Word × Word) :=
  (slot, value) :: storage.filter fun (candidate, _) => candidate != slot

def modelTransaction (step : Aggregates.CheckedDAG) (fuel mask keyMask : Nat) (prior : List (Word × Word))
    (transaction : Transaction) : Option ModelRow := Id.run do
  let limit := iterations mask transaction.input
  let base := transaction.input.bitAnd (Word.ofNatModulo KeccakLoop.highMask)
  let accumulator := Word.ofNatModulo KeccakLoop.accumulatorSlot
  let mut storage := prior
  let mut logs : Array ModelLog := #[]
  let mut counter := 0
  let mut failed := false
  -- At most the largest mask's iterations; the guard keeps the loop structural.
  for _ in List.range KeccakLoop.maxIterations do
    if !failed && limit > counter then
      let current := base.bitOr (Word.ofNatModulo (counter &&& keyMask))
      let slot := entrySlot current
      match stepResult step fuel (lookup storage slot + lookup storage accumulator + transaction.input) with
      | some value =>
          storage := update (update storage slot value) accumulator value
          logs := logs.push ⟨counter, current, value⟩
          counter := counter + 1
      | none => failed := true
  if failed then return none
  let result := lookup storage accumulator + Word.ofNatModulo limit
  let reverted := transaction.flags.val % 2 == 1
  return some ⟨reverted, result, if reverted then prior else storage, if reverted then [] else logs.toList⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (fuel mask keyMask : Nat) (transactions : List Transaction) :
    Option (List ModelRow) := Id.run do
  let mut storage : List (Word × Word) := []
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step fuel mask keyMask storage transaction with
    | some row =>
        rows := rows.push row
        storage := row.storage
    | none => return none
  return some rows.toList

/-- A modelled row's value at each observed slot. -/
def modelSlots (row : ModelRow) (slots : List Word) : List Word := slots.map (lookup row.storage)

end Solcore.Synthesis.Stateful.KeccakLoopExecution
