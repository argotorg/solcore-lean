import Solcore.Test.Adr0149TopLevelLogsFixture

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
  | .outOfFuel _ _ _ _ _ =>
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
  | .outOfFuel _ _ _ _ _ =>
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
  | .outOfFuel _ _ _ _ _ =>
      throw (IO.userError "trapping log program must complete")
  | .completed result =>
      assertTrue (result.outcome == .trapped trapReason)
        "trapping log program produced the wrong root outcome"
      assertExactWorkingLogs result
        "trap must retain the exact speculative log sequence"
      assertTrue (result.committedJournal.logList == [])
        "trap must select the empty root checkpoint journal"

/-- Find a genuine exhaustion point after exactly the first log was handled. -/
private def findOneLogSplit : Nat → Nat → Option Nat
  | _, 0 => none
  | fuel, remaining + 1 =>
      match runWith returnSelector fuel with
      | .completed _ => none
      | .outOfFuel context _ _ _ _ =>
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
  | .outOfFuel context _ _ _ _ =>
      assertTrue (context.workingJournal.logList == [firstLog])
        "exhausted context must retain the first log exactly once"
      match TopLevelExecution.resumeWithFuel prefixRun 256 with
      | .outOfFuel _ _ _ _ _ =>
          throw (IO.userError "resumed log program must complete")
      | .completed resumed =>
          assertTrue (resumed.workingJournal.logList == expectedLogs)
            "resumption must append only the second log without replay"
          assertTrue (resumed.committedJournal.logList == expectedLogs)
            "resumed return must commit the exact once-only log sequence"
          match runWith returnSelector 256 with
          | .outOfFuel _ _ _ _ _ =>
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
  testReturnedLogs
  testRevertedLogs
  testTrappedLogs
  testOutOfFuelExactlyOnce

end Tests.Adr0149TopLevelLogs
