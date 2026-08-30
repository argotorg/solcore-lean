import Solcore.Test.Adr0149TopLevelLogsFixture
import Solcore.Core.HostRunner
import Solcore.Semantics.HostDriverResumption
import Solcore.Semantics.HostStorageDriver

/-! Executable root commit/rollback and resumption tests for ADR-0149 logs. -/

set_option autoImplicit false

namespace Tests.Adr0149TopLevelLogs

open Solcore.Core
open Solcore.Semantics
open Adr0149TopLevelLogsFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def assertExactWorkingLogs
    (result : TopLevelTerminalResult initialWorld targetAddress)
    (message : String) : IO Unit := do
  assertTrue (result.workingJournal.logList == expectedLogs) message
  assertTrue
    (result.terminalContext.workingJournal.logList == expectedLogs)
    "terminal context and exposed speculative logs must agree exactly"
  assertTrue (result.workingJournal.createdContractList == [])
    "word-log execution must not invent contract-creation observations"
  assertTrue
    (result.workingJournal.logList.length == 2 && firstLog == secondLog)
    "two identical emissions must remain two ordered journal entries"

private def testReturnedLogs : IO Unit := do
  match runWith returnSelector 256 with
  | .outOfFuel _ _ _ _ _ _ =>
      throw (IO.userError "returning log program must complete")
  | .completed result =>
      assertTrue
        (result.outcome == .returned (encodeWordBytesBE returnPayload))
        "returning log program produced the wrong root outcome"
      assertExactWorkingLogs result
        "return must expose emitter/topic/payload in chronological order"
      assertTrue (result.committedJournal.logList == expectedLogs)
        "return must commit both emitted logs in exact order"

private def testRevertedLogs : IO Unit := do
  match runWith revertSelector 256 with
  | .outOfFuel _ _ _ _ _ _ =>
      throw (IO.userError "reverting log program must complete")
  | .completed result =>
      assertTrue
        (result.outcome == .reverted (encodeWordBytesBE revertPayload))
        "reverting log program produced the wrong root outcome"
      assertExactWorkingLogs result
        "revert must retain the exact speculative log sequence"
      assertTrue (result.committedJournal.logList == [])
        "revert must select the empty root checkpoint journal"

private def testTrappedLogs : IO Unit := do
  match runWith trapSelector 256 with
  | .outOfFuel _ _ _ _ _ _ =>
      throw (IO.userError "trapping log program must complete")
  | .completed result =>
      assertTrue (result.outcome == .trapped trapReason)
        "trapping log program produced the wrong root outcome"
      assertExactWorkingLogs result
        "trap must retain the exact speculative log sequence"
      assertTrue (result.committedJournal.logList == [])
        "trap must select the empty root checkpoint journal"

private def legacyFuel : Nat := 256
private def resumedFuel : Nat := 37

private def sameJournal
    (left right : TransactionJournal) : Bool :=
  left.logList == right.logList &&
    left.createdContractList == right.createdContractList

private def testLegacyLogIsExplicitlyUnsupported : IO Unit := do
  let initialContext := TopLevelExecution.initialTransactionContext installed
  let inputs := (invocationWith returnSelector).executionInputs
  let initialState := State.initial code.program.body hostEnvironment
  let coreResult := hostRun legacyFuel initialState
  let legacyResult := code.runWithStorage initialContext inputs legacyFuel
  match coreResult, legacyResult with
  | .suspended emitted emittedRemainingFuel,
      ⟨rejectedContext, .unsupported rejected rejectedRemainingFuel⟩ =>
      assertTrue (emitted == rejected)
        "legacy rejection must preserve the exact Core suspension"
      assertTrue (rejected.request == .emitLogWord firstTopic firstPayload)
        "legacy rejection must expose the exact log request"
      assertTrue (emittedRemainingFuel == rejectedRemainingFuel)
        "legacy rejection must preserve Core's remaining fuel"
      assertTrue
        (rejectedContext.context.storageAddress ==
          initialContext.context.storageAddress)
        "legacy rejection must preserve the selected storage address"
      assertTrue
        (sameJournal
          (TransactionHostStorageDriver.Context.workingJournal rejectedContext)
          initialContext.workingJournal)
        "legacy rejection must leave the working journal unchanged"
      assertTrue
        (sameJournal
          rejectedContext.context.values.checkpoint.effects.rollback
          initialContext.context.values.checkpoint.effects.rollback)
        "legacy rejection must leave the checkpoint journal unchanged"
      let resumed := legacyResult.resumeWithFuel
        (TransactionHostStorageDriver.handler inputs) resumedFuel
      match resumed with
      | ⟨resumedContext,
          .unsupported resumedSuspension resumedRemainingFuel⟩ =>
          assertTrue (resumedSuspension == rejected)
            "resumption must retain the unsupported suspension"
          assertTrue
            (resumedRemainingFuel == rejectedRemainingFuel + resumedFuel)
            "resumption must retain and extend the unused fuel exactly"
          assertTrue
            (sameJournal
              (TransactionHostStorageDriver.Context.workingJournal
                resumedContext)
              initialContext.workingJournal)
            "resumption must not invoke even a log-capable handler"
      | _ =>
          throw (IO.userError
            "resumption must not cross an unsupported legacy boundary")
  | _, _ =>
      throw (IO.userError
        "legacy checked execution must stop explicitly at its first log")

private def testSameCodeRecordsLogsTransactionally : IO Unit := do
  let initialContext := TopLevelExecution.initialTransactionContext installed
  let inputs := (invocationWith returnSelector).executionInputs
  match code.runWithTransactionStorage initialContext inputs legacyFuel with
  | ⟨finalContext, .done _ _⟩ =>
      assertTrue (finalContext.workingJournal.logList == expectedLogs)
        "transaction execution must record every log from the same code"
  | _ =>
      throw (IO.userError
        "transaction execution of the checked log program must complete")

/-- Find a genuine exhaustion point after exactly the first log was handled. -/
private def findOneLogSplit : Nat → Nat → Option Nat
  | _, 0 => none
  | fuel, remaining + 1 =>
      match runWith returnSelector fuel with
      | .completed _ => none
      | .outOfFuel context _ _ _ _ _ =>
          if context.workingJournal.logList == [firstLog]
            then some fuel
            else findOneLogSplit (fuel + 1) remaining

private def testOutOfFuelExactlyOnce : IO Unit := do
  let splitFuel ←
    match findOneLogSplit 0 256 with
    | some fuel => pure fuel
    | none =>
        throw (IO.userError
          "no exhausted boundary retained exactly the first emitted log")
  let prefixRun := runWith returnSelector splitFuel
  match prefixRun with
  | .completed _ =>
      throw (IO.userError "selected log split must remain exhausted")
  | .outOfFuel context _ _ _ _ _ =>
      assertTrue (context.workingJournal.logList == [firstLog])
        "exhausted context must retain the first log exactly once"
      match TopLevelExecution.resumeWithFuel prefixRun 256 with
      | .outOfFuel _ _ _ _ _ _ =>
          throw (IO.userError "resumed log program must complete")
      | .completed resumed =>
          assertTrue (resumed.workingJournal.logList == expectedLogs)
            "resumption must append only the second log without replay"
          assertTrue (resumed.committedJournal.logList == expectedLogs)
            "resumed return must commit the exact once-only log sequence"
          match runWith returnSelector 256 with
          | .outOfFuel _ _ _ _ _ _ =>
              throw (IO.userError "one-shot comparison must complete")
          | .completed oneShot =>
              assertTrue
                (resumed.outcome == oneShot.outcome &&
                  resumed.workingJournal.logList ==
                    oneShot.workingJournal.logList &&
                  resumed.committedJournal.logList ==
                    oneShot.committedJournal.logList)
                "split and one-shot log executions must be observationally exact"

def testAdr0149TopLevelLogs : IO Unit := do
  testLegacyLogIsExplicitlyUnsupported
  testSameCodeRecordsLogsTransactionally
  testReturnedLogs
  testRevertedLogs
  testTrappedLogs
  testOutOfFuelExactlyOnce

end Tests.Adr0149TopLevelLogs
