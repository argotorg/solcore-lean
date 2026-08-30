import Solcore.Core.Primitive
import Solcore.Semantics.TransactionJournalProperties

/-! Executable tests for ordered rollback-scoped transaction observations. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def address (value : Nat) : Address :=
  ⟨value % addressModulus, Nat.mod_lt _ (by decide)⟩

private def word (value : Nat) : Word :=
  Word.ofNatModulo value

private def firstLog : CheckedCoreWordLog := {
  emitter := address 17
  topic := word 23
  payload := word 29
}

private def secondLog : CheckedCoreWordLog := {
  emitter := address 31
  topic := word 37
  payload := word 41
}

def testTransactionJournal : IO Unit := do
  let empty := TransactionJournal.empty
  assertTrue
    (empty.logList.isEmpty && empty.createdContractList.isEmpty)
    "an empty transaction journal must expose no logs or creations"

  let withDuplicateLogs :=
    (empty.recordLog firstLog).recordLog firstLog
  assertTrue
    (withDuplicateLogs.logList == [firstLog, firstLog])
    "log recording must preserve chronological order and duplicates"
  assertTrue
    withDuplicateLogs.createdContractList.isEmpty
    "log recording must not add a creation observation"

  let firstCreated := address 43
  let secondCreated := address 47
  let withFirstCreation :=
    withDuplicateLogs.recordCreatedContract firstCreated
  let completed :=
    (withFirstCreation.recordLog secondLog).recordCreatedContract secondCreated
  assertTrue
    (completed.logList == [firstLog, firstLog, secondLog])
    "creation recording must leave the ordered log trace unchanged"
  assertTrue
    (completed.createdContractList == [firstCreated, secondCreated])
    "successful creations must be observed in completion order"
  assertTrue
    (completed.logList[0]? == some {
      emitter := address 17
      topic := word 23
      payload := word 29
    })
    "a recorded log must retain its exact emitter, topic, and payload"

end Tests
