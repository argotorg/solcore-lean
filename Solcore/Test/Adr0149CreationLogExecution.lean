import Solcore.Test.Adr0149CreationLogExecutionFixture

/-! Runtime regressions for creation-scoped logs and creation observations. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.OneLevelNestedExecution
open Adr0148CreationEndToEndFixture
open Adr0149CreationLogExecutionFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def completionFuel : Nat := 512

private def successfulInitializer : CheckedCoreWordOutcome :=
  .returned initializerInput

private def revertedInitializer : CheckedCoreWordOutcome :=
  .reverted initializerInput

private def trappedInitializer : CheckedCoreWordOutcome :=
  .trapped initializerInput

private def successfulCreationJournals : Bool :=
  match (runScenario .commit successfulInitializer completionFuel).view with
  | .outOfFuel _ _ _ => false
  | .completed terminal =>
      terminal.outcome ==
          .returned (encodeWordBytesBE (addressToWord created)) &&
        terminal.workingJournal.logList == successfulLogs &&
        terminal.committedJournal.logList == successfulLogs &&
        terminal.workingJournal.createdContractList == [created] &&
        terminal.committedJournal.createdContractList == [created] &&
        terminal.finalWorld.nonce? creator == some ⟨8, by decide⟩

private def failedInitializerRollsBack
    (outcome : CheckedCoreWordOutcome) : Bool :=
  match (runScenario .catchFailure outcome completionFuel).view with
  | .outOfFuel _ _ _ => false
  | .completed terminal =>
      terminal.workingJournal.logList == failedInitializerLogs &&
        terminal.committedJournal.logList == failedInitializerLogs &&
        terminal.workingJournal.createdContractList == [] &&
        terminal.committedJournal.createdContractList == [] &&
        terminal.finalWorld.nonce? creator == some ⟨8, by decide⟩ &&
        (terminal.finalWorld.account? created).isNone

private def revertedInitializerRollsBack : Bool :=
  failedInitializerRollsBack revertedInitializer

private def trappedInitializerRollsBack : Bool :=
  failedInitializerRollsBack trappedInitializer

private def laterRootRollback
    (disposition : RootDisposition)
    (expected : FrameOutcome Word) : Bool :=
  match (runScenario disposition successfulInitializer completionFuel).view with
  | .outOfFuel _ _ _ => false
  | .completed terminal =>
      terminal.outcome == expected &&
        terminal.workingJournal.logList == successfulLogs &&
        terminal.workingJournal.createdContractList == [created] &&
        terminal.committedJournal.logList == [] &&
        terminal.committedJournal.createdContractList == [] &&
        terminal.finalWorld.nonce? creator == some oldNonce &&
        (terminal.finalWorld.account? created).isNone

private def laterRootRevertRollsBack : Bool :=
  laterRootRollback .revert
    (.reverted (encodeWordBytesBE rootRevertReason))

private def laterRootTrapRollsBack : Bool :=
  laterRootRollback .trap (.trapped rootTrapReason)

private def retainedJournal
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation} :
    Mode initialWorld rootContract rootInvocation → TransactionJournal
  | .root frame => frame.context.workingJournal
  | .child frame => frame.childContext.workingJournal
  | .initializer frame => frame.initializerContext.workingJournal

private def validSuccessfulPrefix (journal : TransactionJournal) : Bool :=
  let logs := journal.logList
  let creations := journal.createdContractList
  successfulLogs.take logs.length == logs &&
    (creations == [] || creations == [created]) &&
    (creations.isEmpty || decide (3 ≤ logs.length))

private def resumedJournalExact (prefixFuel : Nat) : Bool :=
  let prefixResult := runScenario .commit successfulInitializer prefixFuel
  match prefixResult.view with
  | .completed terminal =>
      terminal.workingJournal.logList == successfulLogs &&
        terminal.workingJournal.createdContractList == [created] &&
        terminal.committedJournal.logList == successfulLogs &&
        terminal.committedJournal.createdContractList == [created]
  | .outOfFuel _ mode _ =>
      validSuccessfulPrefix (retainedJournal mode) &&
        (match (resumeWithFuel prefixResult completionFuel).view with
        | .outOfFuel _ _ _ => false
        | .completed terminal =>
            terminal.workingJournal.logList == successfulLogs &&
              terminal.workingJournal.createdContractList == [created] &&
              terminal.committedJournal.logList == successfulLogs &&
              terminal.committedJournal.createdContractList == [created])

private def everyOutOfFuelBoundaryIsExactlyOnce : Bool :=
  (List.range 180).all resumedJournalExact

private def initializerPrefixVisible (fuel : Nat) : Bool :=
  match (runScenario .commit successfulInitializer fuel).view with
  | .outOfFuel _ (.initializer frame) _ =>
      frame.initializerContext.workingJournal.logList ==
        [rootLogBefore, initializerLogFirst, initializerLogSecond]
  | _ => false

private def completedCreationVisibleBeforeRootLog (fuel : Nat) : Bool :=
  match (runScenario .commit successfulInitializer fuel).view with
  | .outOfFuel _ (.root frame) _ =>
      frame.context.workingJournal.createdContractList == [created] &&
        frame.context.workingJournal.logList ==
          [rootLogBefore, initializerLogFirst, initializerLogSecond]
  | _ => false

private def criticalBoundariesAreVisible : Bool :=
  (List.range 180).any initializerPrefixVisible &&
    (List.range 180).any completedCreationVisibleBeforeRootLog

private def sequentialCreationsPreserveCompletionOrder : Bool :=
  match (runSequentialCreations completionFuel).view with
  | .outOfFuel _ _ _ => false
  | .completed terminal =>
      terminal.outcome ==
          .returned (encodeWordBytesBE (addressToWord secondCreated)) &&
        terminal.workingJournal.logList == sequentialInitializerLogs &&
        terminal.committedJournal.logList == sequentialInitializerLogs &&
        terminal.workingJournal.createdContractList ==
          [created, secondCreated] &&
        terminal.committedJournal.createdContractList ==
          [created, secondCreated] &&
        terminal.finalWorld.nonce? creator == some ⟨9, by decide⟩ &&
        (terminal.finalWorld.code? created).isSome &&
        (terminal.finalWorld.code? secondCreated).isSome

private def preflightFailureLeavesJournalIdentity
    (environment : ExecutionEnvironment) : Bool :=
  match (runWithSelectedEnvironment .catchFailure environment
      completionFuel).view with
  | .outOfFuel _ _ _ => false
  | .completed terminal =>
      terminal.workingJournal.logList == failedInitializerLogs &&
        terminal.committedJournal.logList == failedInitializerLogs &&
        terminal.workingJournal.createdContractList == [] &&
        terminal.committedJournal.createdContractList == [] &&
        terminal.finalWorld.nonce? creator == some oldNonce &&
        (terminal.finalWorld.account? created).isNone

private def checkedPreflightFailuresLeaveJournalIdentity : Bool :=
  [unavailableCreationEnvironment, collisionCreationEnvironment].all
    preflightFailureLeavesJournalIdentity

private def insufficientBalanceLeavesJournalIdentity : Bool :=
  match (runWithInsufficientBalance completionFuel).view with
  | .outOfFuel _ _ _ => false
  | .completed terminal =>
      terminal.workingJournal.logList == failedInitializerLogs &&
        terminal.committedJournal.logList == failedInitializerLogs &&
        terminal.workingJournal.createdContractList == [] &&
        terminal.committedJournal.createdContractList == [] &&
        terminal.finalWorld.nonce? creator == some oldNonce &&
        terminal.finalWorld.balance? creator ==
          some insufficientCreatorBalance &&
        (terminal.finalWorld.account? created).isNone

private theorem compileTimeCreationJournals :
    successfulCreationJournals && revertedInitializerRollsBack &&
      trappedInitializerRollsBack && laterRootRevertRollsBack &&
      laterRootTrapRollsBack = true := by
  native_decide

private theorem compileTimeCreationResumption :
    everyOutOfFuelBoundaryIsExactlyOnce && criticalBoundariesAreVisible = true := by
  native_decide

private theorem compileTimeSequentialCreationOrder :
    sequentialCreationsPreserveCompletionOrder = true := by
  native_decide

private theorem compileTimePreflightJournalIdentity :
    checkedPreflightFailuresLeaveJournalIdentity &&
      insufficientBalanceLeavesJournalIdentity = true := by
  native_decide

def testAdr0149CreationLogExecution : IO Unit := do
  assertTrue successfulCreationJournals
    "initializer logs or the successful creation observation were not committed"
  assertTrue revertedInitializerRollsBack
    "initializer revert retained logs or a successful-creation observation"
  assertTrue trappedInitializerRollsBack
    "initializer trap retained logs or a successful-creation observation"
  assertTrue laterRootRevertRollsBack
    "root revert committed speculative initializer observations"
  assertTrue laterRootTrapRollsBack
    "root trap committed speculative initializer observations"
  assertTrue everyOutOfFuelBoundaryIsExactlyOnce
    "creation resumption duplicated, lost, or reordered transaction observations"
  assertTrue criticalBoundariesAreVisible
    "initializer/completion boundaries did not expose their retained journal"
  assertTrue sequentialCreationsPreserveCompletionOrder
    "sequential creations lost completion-order logs or created addresses"
  assertTrue checkedPreflightFailuresLeaveJournalIdentity
    "a checked creation preflight failure changed transaction observations"
  assertTrue insufficientBalanceLeavesJournalIdentity
    "insufficient creation balance changed journal, nonce, or world state"

end Tests
