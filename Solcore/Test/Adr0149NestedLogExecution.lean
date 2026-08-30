import Solcore.Test.Adr0149NestedLogExecutionFixture

/-! Runtime regressions for nested transaction-log ordering and rollback. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open Adr0149NestedLogExecutionFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def completionFuel : Nat := 512

private def returnedChild : CheckedCoreWordOutcome :=
  .returned returnPayload

private def revertedChild : CheckedCoreWordOutcome :=
  .reverted revertPayload

private def trappedChild : CheckedCoreWordOutcome :=
  .trapped trapReason

private def allLogs : List CheckedCoreWordLog :=
  [rootBeforeLog, childLog, rootAfterLog]

private def parentOnlyLogs : List CheckedCoreWordLog :=
  [rootBeforeLog, rootAfterLog]

private def logsMatch
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : OneLevelNestedExecution.Result
      initialWorld rootContract rootInvocation)
    (outcome : FrameOutcome Word)
    (working committed : List CheckedCoreWordLog) : Bool :=
  match result.view with
  | .completed terminal =>
      terminal.outcome == outcome &&
        terminal.workingJournal.logList == working &&
        terminal.committedJournal.logList == committed
  | .outOfFuel _ _ _ => false

private def parentChildParentOrder : Bool :=
  logsMatch
    (runScenario .returned returnedChild completionFuel)
    (.returned (encodeWordBytesBE returnPayload)) allLogs allLogs

private def revertedChildLogsRollBack : Bool :=
  logsMatch
    (runScenario .returned revertedChild completionFuel)
    (.returned (encodeWordBytesBE returnPayload))
    parentOnlyLogs parentOnlyLogs

private def trappedChildLogsRollBack : Bool :=
  logsMatch
    (runScenario .returned trappedChild completionFuel)
    (.returned (encodeWordBytesBE returnPayload))
    parentOnlyLogs parentOnlyLogs

private def laterRootRevertRollsBackAllLogs : Bool :=
  logsMatch
    (runScenario .reverted returnedChild completionFuel)
    (.reverted (encodeWordBytesBE revertPayload))
    allLogs []

private def laterRootTrapRollsBackAllLogs : Bool :=
  logsMatch
    (runScenario .trapped returnedChild completionFuel)
    (.trapped trapReason) allLogs []

private def retainedLogs
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation} :
    OneLevelNestedExecution.Mode
      initialWorld rootContract rootInvocation →
      List CheckedCoreWordLog
  | .root frame => frame.context.workingJournal.logList
  | .child frame => frame.childContext.workingJournal.logList
  | .initializer frame => frame.initializerContext.workingJournal.logList

private def isExpectedPrefix (logs : List CheckedCoreWordLog) : Bool :=
  allLogs.take logs.length == logs

private def resumedLogsExact (prefixFuel : Nat) : Bool :=
  let prefixResult := runScenario .returned returnedChild prefixFuel
  match prefixResult.view with
  | .completed terminal =>
      terminal.workingJournal.logList == allLogs &&
        terminal.committedJournal.logList == allLogs
  | .outOfFuel _ mode _ =>
      isExpectedPrefix (retainedLogs mode) &&
        logsMatch
          (OneLevelNestedExecution.resumeWithFuel prefixResult completionFuel)
          (.returned (encodeWordBytesBE returnPayload)) allLogs allLogs

private def everyOutOfFuelBoundaryIsExactlyOnce : Bool :=
  (List.range 160).all resumedLogsExact

private def childOutOfFuelAfterItsLog (fuel : Nat) : Bool :=
  match (runScenario .returned returnedChild fuel).view with
  | .outOfFuel _ (.child frame) _ =>
      frame.childContext.workingJournal.logList ==
        [rootBeforeLog, childLog]
  | _ => false

private def loggedChildOutOfFuelIsVisible : Bool :=
  (List.range 160).any childOutOfFuelAfterItsLog

private theorem compileTimeParentChildParentOrder :
    parentChildParentOrder = true := by
  native_decide

private theorem compileTimeRevertedChildRollback :
    revertedChildLogsRollBack = true := by
  native_decide

private theorem compileTimeTrappedChildRollback :
    trappedChildLogsRollBack = true := by
  native_decide

private theorem compileTimeLaterRootRevertRollback :
    laterRootRevertRollsBackAllLogs = true := by
  native_decide

private theorem compileTimeLaterRootTrapRollback :
    laterRootTrapRollsBackAllLogs = true := by
  native_decide

private theorem compileTimeEveryOutOfFuelBoundaryExactlyOnce :
    everyOutOfFuelBoundaryIsExactlyOnce = true := by
  native_decide

private theorem compileTimeLoggedChildOutOfFuelVisible :
    loggedChildOutOfFuelIsVisible = true := by
  native_decide

def testAdr0149NestedLogExecution : IO Unit := do
  assertTrue parentChildParentOrder
    "root/child/root logs were not preserved in chronological order"
  assertTrue revertedChildLogsRollBack
    "a reverted child's log survived its call checkpoint"
  assertTrue trappedChildLogsRollBack
    "a trapped child's log survived its call checkpoint"
  assertTrue laterRootRevertRollsBackAllLogs
    "root revert committed speculative parent and child logs"
  assertTrue laterRootTrapRollsBackAllLogs
    "root trap committed speculative parent and child logs"
  assertTrue everyOutOfFuelBoundaryIsExactlyOnce
    "resumption duplicated, lost, or reordered a retained log prefix"
  assertTrue loggedChildOutOfFuelIsVisible
    "no retained child state exposed its already-recorded log"

end Tests
