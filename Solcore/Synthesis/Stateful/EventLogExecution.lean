import Solcore.Synthesis.Core.EventLog
import Solcore.Synthesis.Stateful.KeyedStorageExecution

/-! Execute the original checked event-log contract over a persistent account
world. Each invocation starts a fresh Core heap and an empty transaction
journal; only the public terminal `finalWorld` becomes the next transaction's
world, and only its `committedJournal` is reported. That journal is the working
journal on return and the checkpoint journal on revert, so rollback is chosen
by `ContractRuntime`, not by this observer. Committed word logs are decoded
into multi-topic logs by `Solcore.Synthesis.Core.EventLog.framingVersion`; a
journal that is not a sequence of complete frames is reported as an observer
failure, never as a shorter log list. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.EventLogExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.EventLog (CheckedPlan headerTag dataTag topicTag maxTopics maxDataWords)

def historySchema : String := "solcore-lean.log-history.v1"

/-- One caller and one installed contract, as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  input : Word
  deriving BEq

/-- The selector of `run(uint256,uint256)`, followed by the flags and the input
as two big-endian Words. Malformed calldata is outside this profile. -/
def inputData (flags input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x73, 0x57, 0xf5, 0xd2] ++ encodeWordBytesBE flags ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags input : Word) : String := encodeBytesText (inputData flags input).bytes

/-- Slot zero holds the step result and slot one the transaction counter. -/
def observedSlots : List Word := [Word.ofNatModulo 0, Word.ofNatModulo 1]

/-- One decoded log: its emitter, topics and data Words in order. -/
structure Event where
  emitter : Address
  topics : List Word
  data : List Word
  deriving BEq, Repr

def eventJson (event : Event) : Json := Json.mkObj [
  ("address", toJson (toString event.emitter.val)),
  ("topics", toJson (event.topics.map fun topic => toString topic.val)),
  ("data", toJson (encodeBytesText (event.data.foldl (fun bytes value => bytes ++ encodeWordBytesBE value) ByteArray.empty)))]

def eventsJson (events : List Event) : Json := toJson (events.map eventJson)

/-- Read `count` records numbered from one under `tag`, all from `emitter`. -/
private def tagged (emitter : Address) (tag : Nat → Nat) (count : Nat) (records : List CheckedCoreWordLog) :
    Except String (List Word × List CheckedCoreWordLog) := do
  let mut rest := records
  let mut values : Array Word := #[]
  for index in List.range count do
    match rest with
    | [] => throw "truncated log frame"
    | record :: tail =>
        unless record.emitter == emitter do throw "log frame mixes emitters"
        unless record.topic.val == tag (index + 1) do throw "unexpected log frame record"
        values := values.push record.payload
        rest := tail
  return (values.toList, rest)

/-- Decode a committed journal frame by frame. Every frame consumes at least its
header, so the journal length bounds the loop. -/
def decodeJournal (records : List CheckedCoreWordLog) : Except String (List Event) := do
  let mut rest := records
  let mut events : Array Event := #[]
  for _ in records do
    match rest with
    | [] => pure ()
    | header :: tail =>
        let value := header.topic.val
        unless 256 ≤ value do throw "log frame does not start with a header"
        let dataWords := (value - 256) / 16
        let topics := (value - 256) % 16
        unless dataWords ≤ maxDataWords && topics ≤ maxTopics &&
            value == headerTag {guard := 0, topics, dataWords} do
          throw "invalid log frame header"
        unless header.payload == Word.zero do throw "log frame header has a nonzero payload"
        let (data, afterData) ← tagged header.emitter dataTag dataWords tail
        let (topicWords, afterTopics) ← tagged header.emitter topicTag topics afterData
        events := events.push {emitter := header.emitter, topics := topicWords, data}
        rest := afterTopics
  unless rest.isEmpty do throw "log journal has records after its frames"
  return events.toList

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => KeyedStorageExecution.storageJson account observedSlots
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation. The code registry is resolved again
against each current committed world, so persistence cannot install a different
contract or retain one invocation's local heap or journal. -/
def observeContract (contract : CheckedCoreContract) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := StorageExecution.initialWorldForContract contract bindings
  let initial := worldStorage world bindings
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
            ("status", toJson "resolution-failure"),
            ("committedStorage", worldStorage prior bindings), ("logs", Json.null)]))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              match decodeJournal terminal.committedJournal.logList with
              | .ok events =>
                  rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                    ("committedStorage", worldStorage world bindings), ("logs", eventsJson events)]))
                  match terminal.outcome with
                  | .trapped _ => stopped := some transaction.id
                  | _ => pure ()
              | .error error =>
                  rows := rows.push (Json.mkObj (common ++ [
                    ("status", toJson "observer-error"), ("detail", toJson error),
                    ("committedStorage", worldStorage world bindings), ("logs", Json.null)]))
                  stopped := some transaction.id
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"),
                ("committedStorage", worldStorage prior bindings), ("logs", Json.null)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", KeyedStorageExecution.slotsJson observedSlots),
    ("framing", toJson Solcore.Synthesis.Core.EventLog.framingVersion),
    ("initialStorage", initial), ("initialLogs", toJson ([] : List Json)), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

end Solcore.Synthesis.Stateful.EventLogExecution
