import Solcore.Test.Adr0147BalancedTopLevelExecutionFixture
import Solcore.Test.Adr0149TopLevelLogsFixture

/-! Balance preflight combined with root log commit, rollback, and resumption. -/

set_option autoImplicit false

namespace Tests.Adr0149BalancedTopLevelLogs

open Solcore.Core
open Solcore.Semantics

open Tests.Adr0147BalancedTopLevelExecutionFixture
open Tests.Adr0149TopLevelLogsFixture

private def executionTargetAddress : Address :=
  Tests.TopLevelExecutionFixture.targetAddress

private def executionCallerAddress : Address :=
  Tests.TopLevelExecutionFixture.callerAddress

private def returningProgram : Program := {
  resultType := .sum .word (.sum .word .word)
  body :=
    .letE (emitExpr 0 firstTopic firstPayload)
      (.letE (emitExpr 1 secondTopic secondPayload)
        returnedExpr)
}

private theorem returningProgram_checked :
    returningProgram.checkHost = true := by
  decide

private def returningCode : CheckedHostCoreProgram :=
  ⟨returningProgram, returningProgram_checked⟩

private def returningContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 returningCode rfl

private def expectedFirstLog : CheckedCoreWordLog := {
  emitter := executionTargetAddress
  topic := firstTopic
  payload := firstPayload
}

private def expectedSecondLog : CheckedCoreWordLog := {
  emitter := executionTargetAddress
  topic := secondTopic
  payload := secondPayload
}

private def expectedLogs : List CheckedCoreWordLog :=
  [expectedFirstLog, expectedSecondLog]

private def runReturning (callerBalance value : Word) (fuel : Nat) :=
  BalancedTopLevelExecution.run returningContract
    (invocationFrom executionCallerAddress value)
    (installedWithBalances returningContract callerBalance three)
    emptyRegistry fuel

private def runExisting (value : Word) (fuel : Nat) :=
  BalancedTopLevelExecution.run contract
    (invocationFrom executionCallerAddress value)
    (installedWithBalances contract ten three)
    emptyRegistry fuel

private def workingLogs?
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation) :
    Option (List CheckedCoreWordLog) :=
  result.workingJournal?.map TransactionJournal.logList

private def committedLogs?
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation) :
    Option (List CheckedCoreWordLog) :=
  result.committedJournal?.map TransactionJournal.logList

private def terminalBalances?
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation) :
    Option (Option Word × Option Word) :=
  result.finalWorld?.map fun world =>
    (world.balance? executionCallerAddress,
      world.balance? executionTargetAddress)

private def terminalOutcome?
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation) :
    Option (FrameOutcome Word) :=
  match result.terminalStatus? with
  | some (.ok outcome) => some outcome
  | _ => none

private def nonzeroReturnCommitsLogs : Bool :=
  let result := runReturning ten one completionFuel
  terminalOutcome? result ==
      some (.returned (encodeWordBytesBE returnPayload)) &&
    workingLogs? result == some expectedLogs &&
    committedLogs? result == some expectedLogs &&
    terminalBalances? result == some (some nine, some four)

private def rootFailureRollsBackLogs : Bool :=
  let reverted := runExisting one completionFuel
  let trapped := runExisting two completionFuel
  terminalOutcome? reverted ==
      some (.reverted (encodeWordBytesBE revertPayload)) &&
    workingLogs? reverted == some expectedLogs &&
    committedLogs? reverted == some [] &&
    terminalBalances? reverted == some (some ten, some three) &&
    terminalOutcome? trapped == some (.trapped trapReason) &&
    workingLogs? trapped == some expectedLogs &&
    committedLogs? trapped == some [] &&
    terminalBalances? trapped == some (some ten, some three)

private def rejectionIsIdentityWithEmptyJournal : Bool :=
  let result := runReturning zero one completionFuel
  match result.view with
  | .execution _ => false
  | .rejected rejected =>
      rejected.failure == .insufficientBalance &&
        rejected.finalWorld.balance? executionCallerAddress == some zero &&
        rejected.finalWorld.balance? executionTargetAddress == some three &&
        rejected.committedDelta.balanceChange? executionCallerAddress == none &&
        rejected.committedDelta.balanceChange? executionTargetAddress == none &&
        rejected.committedJournal.logList == [] &&
        workingLogs? result == some [] && committedLogs? result == some []

private def zeroValuePreservesJournalExecution : Bool :=
  let result :=
    BalancedTopLevelExecution.run returningContract
      (invocationFrom executionCallerAddress zero)
      (installedWithoutCaller returningContract three)
      emptyRegistry completionFuel
  terminalOutcome? result ==
      some (.returned (encodeWordBytesBE returnPayload)) &&
    workingLogs? result == some expectedLogs &&
    committedLogs? result == some expectedLogs &&
    terminalBalances? result == some (none, some three)

private def inFlightLogs?
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation) :
    Option (List CheckedCoreWordLog) :=
  match result.view with
  | .rejected _ => none
  | .execution execution =>
      match execution.view with
      | .completed _ => none
      | .outOfFuel _ (.root frame) _ =>
          some frame.context.workingJournal.logList
      | .outOfFuel _ (.child _) _ => none
      | .outOfFuel _ (.initializer _) _ => none

private def findOneLogSplit : Nat → Nat → Option Nat
  | _, 0 => none
  | fuel, remaining + 1 =>
      if inFlightLogs? (runReturning ten one fuel) ==
          some [expectedFirstLog]
      then some fuel
      else findOneLogSplit (fuel + 1) remaining

private def splitResumeIsExactlyOnce : Bool :=
  match findOneLogSplit 0 256 with
  | none => false
  | some splitFuel =>
      let prefixRun := runReturning ten one splitFuel
      let resumed :=
        BalancedTopLevelExecution.resumeWithFuel prefixRun completionFuel
      let oneShot :=
        runReturning ten one completionFuel
      prefixRun.workingJournal?.isNone && prefixRun.committedJournal?.isNone &&
        inFlightLogs? prefixRun == some [expectedFirstLog] &&
        workingLogs? resumed == some expectedLogs &&
        committedLogs? resumed == some expectedLogs &&
        workingLogs? resumed == workingLogs? oneShot &&
        committedLogs? resumed == committedLogs? oneShot &&
        terminalBalances? resumed == some (some nine, some four)

private theorem allScenarios_exact :
    nonzeroReturnCommitsLogs && rootFailureRollsBackLogs &&
      rejectionIsIdentityWithEmptyJournal &&
      zeroValuePreservesJournalExecution && splitResumeIsExactlyOnce = true := by
  native_decide

def testAdr0149BalancedTopLevelLogs : IO Unit := do
  unless nonzeroReturnCommitsLogs do
    throw (IO.userError "nonzero root return did not commit ordered logs")
  unless rootFailureRollsBackLogs do
    throw (IO.userError "root failure did not roll logs and balances back")
  unless rejectionIsIdentityWithEmptyJournal do
    throw (IO.userError "transfer rejection did not expose an empty journal")
  unless zeroValuePreservesJournalExecution do
    throw (IO.userError "zero-value journal execution diverged from the nested path")
  unless splitResumeIsExactlyOnce do
    throw (IO.userError "balanced log resumption duplicated transfer or logs")

end Tests.Adr0149BalancedTopLevelLogs
