import Solcore.ContractRuntime.Internal.NestedLaws
import Solcore.ContractRuntime.Internal.BalancedLaws
import Solcore.Test.ContractRuntime.SelectedExecution
import Solcore.ContractRuntime.Internal.ParentIndexedExecution
import Solcore.ContractRuntime.Internal.WorldStateLaws
import Solcore.ContractRuntime.Internal.StorageDriverLaws
import Solcore.ContractRuntime.Internal.ContractLaws
import Solcore.Test.ContractRuntime.Creation
import Solcore.Test.ContractRuntime.NestedExecution
import Solcore.ContractRuntime.Internal.TopLevelLaws
import Solcore.ContractRuntime.WorldState

/-!
# Top-level execution tests

Checked root execution: observations, the current address, balance-aware atomic roots and the sealed
execution environment.
-/

section
-- leanmerge: from Solcore.Test.Adr0147BalancedRootExternalProperties
/-! External compile consumers for post-transfer root initialization laws. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime
open OneLevelNestedExecution

variable {checkpointWorld workingWorld : WorldState}
variable {rootContract : CheckedCoreContract}
variable {rootInvocation : TopLevelInvocation}
variable
  (installed :
    InstalledCheckedCoreContract workingWorld rootInvocation.target
      rootContract)

example :
    (RootFrame.prepared (checkpointWorld := checkpointWorld) rootContract
      rootInvocation installed).context.context.storageAddress =
        rootInvocation.target :=
  RootFrame.prepared_storageAddress installed

example :
    (RootFrame.prepared (checkpointWorld := checkpointWorld) rootContract
      rootInvocation installed).context.context.values.checkpoint.state =
        checkpointWorld :=
  RootFrame.prepared_checkpointState installed

example :
    (RootFrame.prepared (checkpointWorld := checkpointWorld) rootContract
      rootInvocation installed).context.context.values.working.1 =
        workingWorld :=
  RootFrame.prepared_workingState installed

example :
    (RootFrame.prepared (checkpointWorld := checkpointWorld) rootContract
      rootInvocation installed).context.storageAccount = installed.account :=
  RootFrame.prepared_storageAccount installed

example :
    (RootFrame.prepared (checkpointWorld := checkpointWorld) rootContract
      rootInvocation installed).state =
        Core.State.initial rootContract.code.program.body Core.hostEnvironment :=
  RootFrame.prepared_state installed

example (registry : ExecutionEnvironment)
    (transferred :
      checkpointWorld.transferBalance rootInvocation.caller
          rootInvocation.target rootInvocation.callValue =
        .ok workingWorld)
    (initialInstalled :
      InstalledCheckedCoreContract checkpointWorld rootInvocation.target
        rootContract) :
    Reachable registry
      (Mode.preparedRoot (checkpointWorld := checkpointWorld)
        rootContract rootInvocation
        (WorldState.transferBalance_preserves_installed transferred
          initialInstalled)) :=
  .balancedInitial initialInstalled transferred

end Tests
end

section
-- leanmerge: from Solcore.Test.Adr0147BalancedTopLevelExternalProperties
/-! External compile consumers for balance-aware top-level execution laws. -/

set_option autoImplicit false

namespace Tests.Adr0147BalancedTopLevelExternalProperties

open Solcore.ContractRuntime
open BalancedTopLevelExecution

example := @RejectedResult.ofFailure_failure
example := @RejectedResult.ofFailure_finalWorld
example := @RejectedResult.ofFailure_committedDelta
example := @RejectedResult.ofFailure_committedJournal
example := @RejectedResult.committedJournal_eq_empty
example := @RejectedResult.committedDelta_accountEndpoints_identity
example := @RejectedResult.committedDelta_storageEndpoints_identity
example := @RejectedResult.committedDelta_balanceEndpoints_identity
example := @RejectedResult.committedDelta_balanceChange?_identity

example := @Result.eq_of_view_eq
example := @Result.finalWorld?_rejected
example := @Result.terminalStatus?_rejected
example := @Result.committedWorld?_rejected
example := @Result.workingJournal?_rejected
example := @Result.committedJournal?_rejected
example := @Result.finalWorld?_completed
example := @Result.terminalStatus?_completed
example := @Result.committedWorld?_completed
example := @Result.workingJournal?_completed
example := @Result.committedJournal?_completed
example := @Result.observations_outOfFuel

example := @run_of_zero_value
example := @run_of_transfer_failure
example := @run_of_transfer_success
example := @runWithEnvironment_of_zero_value
example := @runWithEnvironment_of_transfer_failure
example := @runWithEnvironment_of_transfer_success
example := @resumeWithFuel_rejected
example := @resumeWithFuel_execution
example := @resumeWithFuel_run
example := @resumeWithFuel_runWithEnvironment
example := @resumeWithFuel_run_zero

end Tests.Adr0147BalancedTopLevelExternalProperties
end

section
-- leanmerge: from Solcore.Test.CurrentAddressExecutionFixture
/-! Shared measured fixture for run-fixed current-address execution tests. -/
set_option autoImplicit false
namespace Tests.CurrentAddressExecutionFixture
open Solcore.Core
open Solcore.ContractRuntime

def codeAddress : Address := ⟨0x10, by decide⟩
def storageAddress : Address := ⟨0x20, by decide⟩
def currentAddress : Address := ⟨0x30, by decide⟩
def alternateCurrentAddress : Address := ⟨0x35, by decide⟩
def callerAddress : Address := ⟨0x40, by decide⟩

def suppliedCallValue : Word := ⟨0x50, by decide⟩
def targetSlot : Word := ⟨0x61, by decide⟩
def oldValue : Word := ⟨0x62, by decide⟩
def retainedSlot : Word := ⟨0x63, by decide⟩
def retainedValue : Word := ⟨0x64, by decide⟩

def inputData : HostStorageDriver.InputData := {
  bytes := [0x11, 0x22, 0x33].toByteArray
  size_lt_wordModulus := by decide
}

def executionInputsFor
    (current : Address) : HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := suppliedCallValue
  callerAddress := callerAddress
  inputData := inputData
  currentAddress := current
}

def executionInputs : HostStorageDriver.ExecutionInputs :=
  executionInputsFor currentAddress
def alternateExecutionInputs : HostStorageDriver.ExecutionInputs :=
  executionInputsFor alternateCurrentAddress

/-- Observe current, write its Word, then observe current again. -/
def program : Program := {
  resultType := .product .word .word
  body :=
    .letE
      (.apply (.var HostFunction.currentAddress.index) .unit)
      (.letE
        (.apply
          (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word targetSlot) (.var 0)))
        (.letE
          (.apply
            (.var (HostFunction.currentAddress.index + 2))
            .unit)
          (.pair (.var 2) (.var 0))))
}

theorem program_host_checked : program.checkHost = true := by decide

def code : CheckedHostCoreProgram := ⟨program, program_host_checked⟩

def storageAccount : Account :=
  Account.empty
    |>.storageWrite targetSlot oldValue
    |>.storageWrite retainedSlot retainedValue

def workingWorld : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress (Account.empty.withCode code)
    |>.putAccount storageAddress storageAccount

def checkpointWorld : WorldState :=
  WorldState.empty.putAccount storageAddress storageAccount

def parentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace Nat) :=
  (checkpointWorld, ⟨101, FrameTrace.empty⟩)

def initialization :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := workingWorld
  workingRollback := 201
}

inductive TrapReason where
  | invalidDoneInputs
  | policyTrap
  deriving Repr, BEq, DecidableEq

def returnData : Bytes := [0xa1, 0xb2].toByteArray
def revertData : Bytes := [0xc1, 0xd2].toByteArray

def expectedWord (current : Address) : Word := addressToWord current
def expectedPair (current : Address) : Value :=
  .pair (.word (expectedWord current)) (.word (expectedWord current))
def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  ParentIndexedSelectedExecutionFixture.storageValueAt? state address slot

def exactCompletion
    (current : Address)
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (value : Value) (store : Store) : Bool :=
  value == expectedPair current && store == [] &&
    context.readStorage targetSlot == expectedWord current

def doneOutcomeFor
    (current : Address) (outcome : FrameOutcome TrapReason)
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (value : Value) (store : Store) : FrameOutcome TrapReason :=
  if exactCompletion current context value store then outcome
  else .trapped .invalidDoneInputs

def returnedDoneOutcomeFor (current : Address) :=
  doneOutcomeFor current (.returned returnData)

def revertedDoneOutcomeFor (current : Address) :=
  doneOutcomeFor current (.reverted revertData)

def trappedDoneOutcomeFor (current : Address) :=
  doneOutcomeFor current (.trapped .policyTrap)

abbrev Result := ParentIndexedSelectedExecutionResult
  Nat Nat TrapReason parentWorking

def runWith
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome TrapReason)
    (fuel : Nat) : Result :=
  initialization.runCodeWithStorageParentIndexedResult
    storageAddress inputs fuel doneOutcome

def resumeWith
    (result : Result) (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome TrapReason)
    (additional : Nat) : Result :=
  result.resumeWithFuel initialization inputs doneOutcome additional

def codeProgramIs (state : WorldState) : Bool :=
  match state.code? codeAddress with
  | some selected => selected.program == program
  | none => false

def accountAbsentAt
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (address : Address) : Bool :=
  (context.context.values.working.1.account? address).isNone &&
    (context.context.values.checkpoint.state.account? address).isNone

def contextPreserved
    (context : HostStorageDriver.Context Nat (FrameTrace Nat)) : Bool :=
  let values := context.context.values
  context.context.storageAddress == storageAddress &&
    codeProgramIs values.working.1 &&
    accountAbsentAt context currentAddress &&
    accountAbsentAt context alternateCurrentAddress &&
    context.storageAccount.storageValue? retainedSlot == some retainedValue &&
    storageValueAt? values.working.1 storageAddress retainedSlot ==
      some retainedValue &&
    storageValueAt? values.checkpoint.state storageAddress targetSlot ==
      some oldValue &&
    storageValueAt? values.checkpoint.state storageAddress retainedSlot ==
      some retainedValue &&
    values.checkpoint.effects.rollback == 101 &&
    values.checkpoint.effects.trace.toList == [] &&
    values.working.2.rollback == 201 &&
    values.working.2.trace.toList == []

def contextHasCurrentWrite
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (current : Address) : Bool :=
  context.readStorage targetSlot == expectedWord current &&
    storageValueAt? context.context.values.working.1
      storageAddress targetSlot == some (expectedWord current)

def currentAddressRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension => suspension.request == .currentAddress
  | _ => false

def storageWriteRequestReady
    (current : Address) (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension =>
      suspension.request == .storageWrite targetSlot (expectedWord current)
  | _ => false

def beforeSecondObservation (state : State) : Bool :=
  state.control == .ret .unit &&
    match state.continuation with
    | [.letBody body _] =>
        body == .letE
          (.apply
            (.var (HostFunction.currentAddress.index + 2)) .unit)
          (.pair (.var 2) (.var 0))
    | _ => false

def oneStepBeforePair (current : Address) (state : State) : Bool :=
  match hostAdvance state with
  | .next next => next == State.final (expectedPair current)
  | _ => false

inductive FoldMarker where
  | returned
  | reverted
  | trapped
  | mismatch
  deriving Repr, BEq, DecidableEq

def foldValuesMatch
    (expectedRollback : Nat) (expectedValue : Word)
    (values : WorldState ×
      FrameEffectJournal Nat (FrameTrace Nat)) : Bool :=
  storageValueAt? values.1 storageAddress targetSlot == some expectedValue &&
    values.2.rollback == expectedRollback &&
    values.2.trace.toList == []

def foldResult
    (current : Address)
    (continuation : ParentIndexedFrameContinuationContext
      Nat Nat TrapReason parentWorking) : FoldMarker :=
  continuation.foldResolutionWithTrapRollback
    (fun values data =>
      if foldValuesMatch 201 (expectedWord current) values &&
          data == returnData then .returned else .mismatch)
    (fun values data =>
      if foldValuesMatch 101 oldValue values &&
          data == revertData then .reverted else .mismatch)
    (fun values reason =>
      if foldValuesMatch 101 oldValue values &&
          reason == .policyTrap then .trapped else .mismatch)

/-- Measured exact boundaries of the executable checked program. -/
def writeRequestFuel : Nat := 16
def postWriteFuel : Nat := 17
def secondRequestFuel : Nat := 23
def pairReadyFuel : Nat := 29
def completionFuel : Nat := 30

end Tests.CurrentAddressExecutionFixture
end

section
-- leanmerge: from Solcore.Test.CurrentAddressExecution
/-! Executable end-to-end regressions for run-fixed current-address input. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open CurrentAddressExecutionFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def returnedPolicy := returnedDoneOutcomeFor currentAddress
private def alternateReturnedPolicy :=
  returnedDoneOutcomeFor alternateCurrentAddress
private def revertedPolicy := revertedDoneOutcomeFor currentAddress
private def trappedPolicy := trappedDoneOutcomeFor currentAddress

private def writeBoundary : Result :=
  runWith executionInputs returnedPolicy writeRequestFuel

private def postWriteOneShot : Result :=
  runWith executionInputs returnedPolicy postWriteFuel

private def secondRequestOneShot : Result :=
  runWith executionInputs returnedPolicy secondRequestFuel

private def pairReadyOneShot : Result :=
  runWith executionInputs returnedPolicy pairReadyFuel

private def completionOneShot : Result :=
  runWith executionInputs returnedPolicy completionFuel

private def largerCompletion : Result :=
  runWith executionInputs returnedPolicy 64

private def alternateCompletion : Result :=
  runWith alternateExecutionInputs alternateReturnedPolicy completionFuel

private def revertedCompletion : Result :=
  runWith executionInputs revertedPolicy completionFuel

private def trappedCompletion : Result :=
  runWith executionInputs trappedPolicy completionFuel

private def postWriteSplit : Result :=
  resumeWith writeBoundary executionInputs returnedPolicy 1

private def completionFromPostWrite : Result :=
  resumeWith postWriteOneShot executionInputs returnedPolicy 13

private def completionFromSecondRequest : Result :=
  resumeWith secondRequestOneShot executionInputs returnedPolicy 7

private def completedResumed : Result :=
  resumeWith completionOneShot executionInputs returnedPolicy 100

private def directState : State :=
  State.initial
    (.apply (.var HostFunction.currentAddress.index) .unit)
    hostEnvironment

private theorem directRunExact
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (inputs : HostStorageDriver.ExecutionInputs) :
    HostStorageDriver.run context inputs 5 directState =
      ⟨context,
        .done (.word (addressToWord inputs.currentAddress)) []⟩ := by
  rw [HostStorageDriver.run_of_suspended_currentAddress
    context inputs 5 0 directState [] [] (by rfl)]
  apply HostStorageDriver.run_of_done
  rfl

private theorem directCurrentOnlyVariationExact
    (context : HostStorageDriver.Context Nat (FrameTrace Nat)) :
    HostStorageDriver.run context executionInputs 5 directState =
        ⟨context, .done (.word (expectedWord currentAddress)) []⟩ ∧
      HostStorageDriver.run context alternateExecutionInputs 5 directState =
        ⟨context,
          .done (.word (expectedWord alternateCurrentAddress)) []⟩ := by
  exact ⟨directRunExact context executionInputs,
    directRunExact context alternateExecutionInputs⟩

private def contextHasTarget
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (expected : Word) : Bool :=
  context.readStorage targetSlot == expected &&
    storageValueAt? context.context.values.working.1
      storageAddress targetSlot == some expected

private def directObservationPasses : Bool :=
  match initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress with
  | none => false
  | some context =>
      match HostStorageDriver.run context executionInputs 4 directState,
          HostStorageDriver.run context executionInputs 5 directState,
          HostStorageDriver.run context executionInputs 64 directState,
          HostStorageDriver.run context alternateExecutionInputs 5 directState with
      | ⟨beforeContext, .outOfFuel beforeState⟩,
          ⟨completedContext, .done value store⟩,
          ⟨largerContext, .done largerValue largerStore⟩,
          ⟨alternateContext, .done alternateValue alternateStore⟩ =>
          contextPreserved beforeContext &&
            contextPreserved completedContext && contextPreserved largerContext &&
            contextPreserved alternateContext &&
            contextHasTarget beforeContext oldValue &&
            contextHasTarget completedContext oldValue &&
            contextHasTarget largerContext oldValue &&
            contextHasTarget alternateContext oldValue &&
            currentAddressRequestReady beforeState &&
            value == .word (expectedWord currentAddress) && store == [] &&
            largerValue == value && largerStore == store &&
            alternateValue ==
              .word (expectedWord alternateCurrentAddress) &&
            alternateValue != value && alternateStore == store
      | _, _, _, _ => false

private def exhaustedAt
    (result : Result) (expected : Word)
    (stateCheck : State → Bool) : Bool :=
  match result with
  | .outOfFuel context state =>
      contextPreserved context && contextHasTarget context expected &&
        stateCheck state
  | _ => false

private def sameExhaustion
    (left right : Result) (expected : Word)
    (stateCheck : State → Bool) : Bool :=
  match left, right with
  | .outOfFuel leftContext leftState,
      .outOfFuel rightContext rightState =>
      contextPreserved leftContext && contextPreserved rightContext &&
        contextHasTarget leftContext expected &&
        contextHasTarget rightContext expected &&
        leftState == rightState &&
        stateCheck leftState && stateCheck rightState
  | _, _ => false

private def completedAs
    (result : Result) (current : Address)
    (marker : FoldMarker) : Bool :=
  match result with
  | .completed context value store continuation =>
      contextPreserved context && contextHasCurrentWrite context current &&
        exactCompletion current context value store &&
        foldResult current continuation == marker
  | _ => false

private def sameCompletion
    (left right : Result) (current : Address)
    (marker : FoldMarker) : Bool :=
  match left, right with
  | .completed leftContext leftValue leftStore leftContinuation,
      .completed rightContext rightValue rightStore rightContinuation =>
      contextPreserved leftContext && contextPreserved rightContext &&
        contextHasCurrentWrite leftContext current &&
        contextHasCurrentWrite rightContext current &&
        exactCompletion current leftContext leftValue leftStore &&
        exactCompletion current rightContext rightValue rightStore &&
        leftValue == rightValue && leftStore == rightStore &&
        foldResult current leftContinuation == marker &&
        foldResult current rightContinuation == marker
  | _, _ => false

private def currentOnlyVariationObserved : Bool :=
  match completionOneShot, alternateCompletion with
  | .completed currentContext currentValue currentStore currentContinuation,
      .completed alternateContext alternateValue alternateStore
        alternateContinuation =>
      executionInputs.codeAddress == alternateExecutionInputs.codeAddress &&
        executionInputs.callValue == alternateExecutionInputs.callValue &&
        executionInputs.callerAddress == alternateExecutionInputs.callerAddress &&
        executionInputs.inputData.bytes ==
          alternateExecutionInputs.inputData.bytes &&
        executionInputs.currentAddress !=
          alternateExecutionInputs.currentAddress &&
        contextPreserved currentContext && contextPreserved alternateContext &&
        exactCompletion currentAddress currentContext
          currentValue currentStore &&
        exactCompletion alternateCurrentAddress alternateContext
          alternateValue alternateStore &&
        currentValue != alternateValue && currentStore == alternateStore &&
        foldResult currentAddress currentContinuation == .returned &&
        foldResult alternateCurrentAddress alternateContinuation == .returned
  | _, _ => false

private def sentinelsAreDistinct : Bool :=
  expectedWord currentAddress != addressToWord codeAddress &&
    expectedWord currentAddress != addressToWord storageAddress &&
    expectedWord currentAddress != addressToWord callerAddress &&
    expectedWord currentAddress != expectedWord alternateCurrentAddress &&
    expectedWord currentAddress != suppliedCallValue &&
    expectedWord currentAddress != inputData.sizeWord

def testCurrentAddressExecution : IO Unit := do
  assertTrue program.checkHost
    "the host checker rejected current-observe/write/observe"
  assertTrue sentinelsAreDistinct
    "the current-address fixture cannot detect an input projection swap"
  assertTrue directObservationPasses
    "the direct current observation moved its 4/5 boundary or changed context"

  assertTrue
    (exhaustedAt writeBoundary oldValue
      (storageWriteRequestReady currentAddress))
    "fuel 16 did not retain the exact current-derived write request"

  let afterWrite := fun state =>
    beforeSecondObservation state &&
      !storageWriteRequestReady currentAddress state
  assertTrue
    (exhaustedAt postWriteOneShot (expectedWord currentAddress) afterWrite &&
      sameExhaustion postWriteSplit postWriteOneShot
        (expectedWord currentAddress) afterWrite)
    "16+1 did not reach the exact post-write suffix without replay"

  let atSecondRequest := fun state =>
    currentAddressRequestReady state &&
      !storageWriteRequestReady currentAddress state
  assertTrue
    (exhaustedAt secondRequestOneShot
      (expectedWord currentAddress) atSecondRequest)
    "fuel 23 did not retain the second current-address request"

  assertTrue
    (exhaustedAt pairReadyOneShot (expectedWord currentAddress)
      (oneStepBeforePair currentAddress))
    "fuel 29 did not stop exactly one step before the result pair"

  assertTrue (completedAs completionOneShot currentAddress .returned)
    "fuel 30 did not preserve the current-derived completion and parent fold"
  assertTrue
    (sameCompletion completionOneShot largerCompletion
      currentAddress .returned)
    "larger fuel changed a completed current-address execution"

  assertTrue
    (sameCompletion completionFromPostWrite completionOneShot
      currentAddress .returned)
    "17+13 did not equal one-shot fuel 30 from the post-write suffix"
  assertTrue
    (sameCompletion completionFromSecondRequest completionOneShot
      currentAddress .returned)
    "23+7 did not equal one-shot fuel 30"
  assertTrue
    (sameCompletion completedResumed completionOneShot
      currentAddress .returned)
    "resuming a completed current-address result changed it"

  assertTrue currentOnlyVariationObserved
    "changing only currentAddress did not change only its derived observations"
  assertTrue (completedAs revertedCompletion currentAddress .reverted)
    "the current-derived completion did not reach the revert fold"
  assertTrue (completedAs trappedCompletion currentAddress .trapped)
    "the current-derived completion did not reach the trap fold"

end Tests
end

section
-- leanmerge: from Solcore.Test.CurrentAddressExecutionSession
/-! Fixed-input session regressions for the current-address execution path. -/

set_option autoImplicit false

namespace Tests.CurrentAddressExecutionSession

open Solcore.Core
open Solcore.ContractRuntime
open CurrentAddressExecutionFixture

abbrev Session := ParentIndexedSelectedExecutionSession
  Nat Nat TrapReason parentWorking

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def startWith
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome TrapReason)
    (fuel : Nat) : Session :=
  ParentIndexedSelectedExecutionSession.start initialization storageAddress
    inputs doneOutcome fuel

private def currentStart : Session :=
  startWith executionInputs (returnedDoneOutcomeFor currentAddress)
    postWriteFuel

private def currentSplit : Session :=
  currentStart.resumeWithFuel (completionFuel - postWriteFuel)

private def currentOneShot : Session :=
  startWith executionInputs (returnedDoneOutcomeFor currentAddress)
    completionFuel

private def alternateOneShot : Session :=
  startWith alternateExecutionInputs
    (returnedDoneOutcomeFor alternateCurrentAddress) completionFuel

private def terminalResumed : Session :=
  currentOneShot.resumeWithFuel 7

private theorem current_zero_exact :
    currentStart.resumeWithFuel 0 = currentStart :=
  ParentIndexedSelectedExecutionSession.resumeWithFuel_zero currentStart

private theorem current_split_exact :
    currentSplit = currentOneShot := by
  unfold currentSplit currentOneShot currentStart startWith
  simpa [postWriteFuel, completionFuel] using
    ParentIndexedSelectedExecutionSession.start_resumeWithFuel
      initialization storageAddress executionInputs
      (returnedDoneOutcomeFor currentAddress) postWriteFuel
      (completionFuel - postWriteFuel)

private theorem current_add_exact :
    (currentStart.resumeWithFuel 6).resumeWithFuel 7 =
      currentStart.resumeWithFuel (6 + 7) :=
  ParentIndexedSelectedExecutionSession.resumeWithFuel_add
    currentStart 6 7

private def exactPostWriteSession (session : Session) : Bool :=
  session.providedFuel == postWriteFuel &&
    session.inputs.currentAddress == currentAddress &&
    match session.result with
    | .outOfFuel context state =>
        contextPreserved context &&
          contextHasCurrentWrite context currentAddress &&
          beforeSecondObservation state &&
          !storageWriteRequestReady currentAddress state
    | _ => false

private def exactCompletionSession
    (current : Address) (session : Session) : Bool :=
  match session.result with
  | .completed context value store continuation =>
      contextPreserved context && contextHasCurrentWrite context current &&
        exactCompletion current context value store &&
        foldResult current continuation == .returned
  | _ => false

private def sameCompletionResult (left right : Session) : Bool :=
  match left.result, right.result with
  | .completed leftContext leftValue leftStore leftContinuation,
      .completed rightContext rightValue rightStore rightContinuation =>
      leftValue == rightValue && leftStore == rightStore &&
        contextHasCurrentWrite leftContext currentAddress &&
        contextHasCurrentWrite rightContext currentAddress &&
        foldResult currentAddress leftContinuation ==
          foldResult currentAddress rightContinuation
  | _, _ => false

def testCurrentAddressExecutionSession : IO Unit := do
  assertTrue (exactPostWriteSession currentStart)
    "the current-address session did not retain the exact fuel-17 state"

  assertTrue
    (currentSplit.providedFuel == completionFuel &&
      currentSplit.inputs.currentAddress == currentAddress &&
      exactCompletionSession currentAddress currentSplit &&
      sameCompletionResult currentSplit currentOneShot)
    "closed session resumption did not equal the fixed-input one-shot run"

  assertTrue
    (alternateOneShot.inputs.codeAddress == executionInputs.codeAddress &&
      alternateOneShot.inputs.callerAddress == executionInputs.callerAddress &&
      alternateOneShot.inputs.callValue == executionInputs.callValue &&
      alternateOneShot.inputs.currentAddress == alternateCurrentAddress &&
      alternateCurrentAddress != currentAddress &&
      exactCompletionSession alternateCurrentAddress alternateOneShot)
    "an alternate current address was not isolated to a distinct start"

  assertTrue
    (terminalResumed.providedFuel == completionFuel + 7 &&
      terminalResumed.inputs.currentAddress == currentAddress &&
      exactCompletionSession currentAddress terminalResumed &&
      sameCompletionResult terminalResumed currentOneShot)
    "resuming completion changed its fixed inputs or terminal result"

end Tests.CurrentAddressExecutionSession

export Tests.CurrentAddressExecutionSession (testCurrentAddressExecutionSession)
end

section
-- leanmerge: from Solcore.Test.CurrentAddressObservationProperties
/-! Compile-only consumers for run-fixed current-address proof contracts. -/

set_option autoImplicit false

namespace Solcore.Test.CurrentAddressObservationProperties

open ContractRuntime
universe u v w x

variable (codeAddress callerAddress currentAddress : Address)
variable (callValue : Core.Word) (inputData : HostStorageDriver.InputData)

example :
    (HostStorageDriver.ExecutionInputs.mk codeAddress callValue callerAddress
      inputData currentAddress).codeAddress = codeAddress :=
  HostStorageDriver.ExecutionInputs.mk_codeAddress
    codeAddress callValue callerAddress inputData currentAddress

example :
    (HostStorageDriver.ExecutionInputs.mk codeAddress callValue callerAddress
      inputData currentAddress).callValue = callValue :=
  HostStorageDriver.ExecutionInputs.mk_callValue
    codeAddress callValue callerAddress inputData currentAddress

example :
    (HostStorageDriver.ExecutionInputs.mk codeAddress callValue callerAddress
      inputData currentAddress).callerAddress = callerAddress :=
  HostStorageDriver.ExecutionInputs.mk_callerAddress
    codeAddress callValue callerAddress inputData currentAddress

example :
    (HostStorageDriver.ExecutionInputs.mk codeAddress callValue callerAddress
      inputData currentAddress).inputData = inputData :=
  HostStorageDriver.ExecutionInputs.mk_inputData
    codeAddress callValue callerAddress inputData currentAddress

example :
    (HostStorageDriver.ExecutionInputs.mk codeAddress callValue callerAddress
      inputData currentAddress).currentAddress = currentAddress :=
  HostStorageDriver.ExecutionInputs.mk_currentAddress
    codeAddress callValue callerAddress inputData currentAddress

example : Core.HostFunction.parameterType .currentAddress = .unit :=
  Core.HostFunction.parameterType_currentAddress

example : Core.HostFunction.resultType .currentAddress = .word :=
  Core.HostFunction.resultType_currentAddress

example : Core.HostFunction.currentAddress ∈ Core.HostFunction.all :=
  Core.HostFunction.mem_all .currentAddress

example : Core.HostFunction.currentAddress.index = 9 :=
  Core.HostFunction.index_currentAddress

example : Core.HostFunction.all.length = 14 :=
  Core.HostFunction.all_length

example : Core.HostFunction.all[9]? = some .currentAddress := by
  simpa using Core.HostFunction.getElem?_all_index .currentAddress

example : Core.hostContext[9]? =
    some (Core.HostFunction.functionType .currentAddress) := by
  simpa using Core.hostContext_currentAddress

example : Core.hostEnvironment[9]? =
    some (.hostFunction .currentAddress) := by
  simpa using Core.hostEnvironment_currentAddress

example : Core.hostContext.length = 14 :=
  Core.hostContext_length

example : Core.hostEnvironment.length = 14 :=
  Core.hostEnvironment_length

example : Core.hostContext[14]? = none :=
  Core.hostContext_firstUnbound

example : Core.hostEnvironment[14]? = none :=
  Core.hostEnvironment_firstUnbound

variable (response : Core.Word)
variable (continuation : List Core.Frame) (store : Core.Store)

example : Core.HostRequest.responseType .currentAddress = .word :=
  Core.HostRequest.responseType_currentAddress

example : Core.HostRequest.responseValue .currentAddress response =
    .word response :=
  Core.HostRequest.responseValue_currentAddress response

example :
    (Core.HostRequest.responseValue .currentAddress response).type =
      Core.HostRequest.responseType .currentAddress :=
  Core.HostRequest.responseValue_type .currentAddress response

example :
    (Core.HostSuspension.mk .currentAddress continuation store).resume response =
      ⟨.ret (.word response), continuation, store⟩ :=
  Core.HostSuspension.resume_currentAddress response continuation store

variable (argument : Core.Expr) (environment : Core.Environment)

example :
    Core.hostAdvance
        ⟨.ret (.hostFunction .currentAddress),
          .applyArgument argument environment :: continuation, store⟩ =
      .next ⟨.eval argument environment,
        .hostApply .currentAddress :: continuation, store⟩ :=
  Core.hostAdvance_begin_currentAddress
    argument environment continuation store

example : Core.HostTransition
    ⟨.ret (.hostFunction .currentAddress),
      .applyArgument argument environment :: continuation, store⟩
    ⟨.eval argument environment,
      .hostApply .currentAddress :: continuation, store⟩ := by
  apply Core.hostAdvance_next_iff.mp
  exact Core.hostAdvance_begin_currentAddress
    argument environment continuation store

example :
    Core.hostAdvance
        ⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩ =
      .suspended ⟨.currentAddress, continuation, store⟩ :=
  Core.hostAdvance_suspend_currentAddress continuation store

example : Core.HostRequestEmission
    ⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩
    ⟨.currentAddress, continuation, store⟩ := by
  apply Core.hostAdvance_suspended_iff.mp
  exact Core.hostAdvance_suspend_currentAddress continuation store

variable (actual : Core.Value) (notUnit : actual ≠ .unit)

example : Core.hostAdvance
      ⟨.ret actual, .hostApply .currentAddress :: continuation, store⟩ =
    .fault (.invalidHostArgument .currentAddress actual) :=
  Core.hostAdvance_invalid_currentAddress_argument
    actual notUnit continuation store

variable {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
variable {value : Core.Value} {resultType : Core.Ty}
variable (valueTyping : Core.HostRuntimeValueHasType world value
  Core.HostFunction.currentAddress.parameterType definitions)

example : ∃ suspension,
    Core.HostRequestEmission
      ⟨.ret value, .hostApply .currentAddress :: continuation, store⟩
      suspension :=
  Core.typed_currentAddress_emits valueTyping

example : Core.HostRuntimeValueHasType world
    (Core.HostRequest.responseValue .currentAddress response)
    (Core.HostRequest.responseType .currentAddress) definitions :=
  Core.HostRequest.responseValue_hasType
    .currentAddress response world definitions

variable (requestStateTyping : Core.HostStateHasType
  ⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩
  resultType definitions)

example : Core.HostSuspensionHasType
    ⟨.currentAddress, continuation, store⟩ resultType definitions :=
  Core.hostRequestEmission_hasType requestStateTyping .currentAddress

example :
    (∃ returnedValue returnedStore,
      (⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩ :
        Core.State) = Core.State.final returnedValue returnedStore) ∨
    (∃ next, Core.HostTransition
      ⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩ next) ∨
    ∃ suspension, Core.HostRequestEmission
      ⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩
      suspension :=
  Core.host_state_progress requestStateTyping

example (error : Core.MachineFault) :
    Core.hostAdvance
      ⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩ ≠
        .fault error :=
  Core.well_typed_host_state_never_faults requestStateTyping

variable (code : CheckedHostCoreProgram) (fuel : Nat)
variable (error : Core.MachineFault) (faultState : Core.State)

example : code.runStateful fuel ≠ .fault error faultState :=
  CheckedHostCoreProgram.runStateful_ne_fault code fuel error faultState

variable {RollbackState : Type u} {TraceState : Type v}
variable (inputs leftInputs rightInputs : HostStorageDriver.ExecutionInputs)
variable (context : HostStorageDriver.Context RollbackState TraceState)

example : HostStorageDriver.handleRequest inputs context .currentAddress =
    (context, addressToWord inputs.currentAddress) :=
  HostStorageDriver.handleRequest_currentAddress inputs context

example : HostStorageDriver.handleSuspension inputs context
      ⟨.currentAddress, continuation, store⟩ =
    (context, ⟨.ret (.word (addressToWord inputs.currentAddress)),
      continuation, store⟩) :=
  HostStorageDriver.handleSuspension_currentAddress
    inputs context continuation store

example : (HostStorageDriver.handleSuspension inputs context
    ⟨.currentAddress, continuation, store⟩).1 = context :=
  HostStorageDriver.handleSuspension_currentAddress_context
    inputs context continuation store

example : (HostStorageDriver.handleSuspension leftInputs context
      ⟨.currentAddress, continuation, store⟩).1 =
    (HostStorageDriver.handleSuspension rightInputs context
      ⟨.currentAddress, continuation, store⟩).1 :=
  HostStorageDriver.handleSuspension_currentAddress_context_independent
    leftInputs rightInputs context continuation store

example : (HostStorageDriver.handleSuspension inputs context
      ⟨.currentAddress, continuation, store⟩).2.control =
    .ret (.word (addressToWord inputs.currentAddress)) :=
  HostStorageDriver.handleSuspension_currentAddress_control
    inputs context continuation store

example :
    (HostStorageDriver.handleSuspension leftInputs context
        ⟨.currentAddress, continuation, store⟩).2.control =
      (HostStorageDriver.handleSuspension rightInputs context
        ⟨.currentAddress, continuation, store⟩).2.control ↔
    leftInputs.currentAddress = rightInputs.currentAddress :=
  HostStorageDriver.handleSuspension_currentAddress_control_eq_iff
    leftInputs rightInputs context continuation store

example : (HostStorageDriver.handleSuspension inputs context
      ⟨.currentAddress, continuation, store⟩).2.continuation = continuation :=
  HostStorageDriver.handleSuspension_currentAddress_continuation
    inputs context continuation store

example : (HostStorageDriver.handleSuspension inputs context
      ⟨.currentAddress, continuation, store⟩).2.store = store :=
  HostStorageDriver.handleSuspension_currentAddress_store
    inputs context continuation store

example : wordToAddress?
      ((HostStorageDriver.handler inputs).handle context .currentAddress).2 =
    some inputs.currentAddress :=
  HostStorageDriver.wordToAddress?_handler_currentAddress inputs context

variable (remainingFuel : Nat) (state : Core.State)
variable (execution : Core.hostRun fuel state =
  .suspended ⟨.currentAddress, continuation, store⟩ remainingFuel)

example : HostStorageDriver.run context inputs fuel state =
    HostStorageDriver.run context inputs remainingFuel
      ⟨.ret (.word (addressToWord inputs.currentAddress)),
        continuation, store⟩ :=
  HostStorageDriver.run_of_suspended_currentAddress
    context inputs fuel remainingFuel state continuation store execution

variable {Event : Type w} {TrapReason : Type x}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
variable (initialization : ParentIndexedFrameInitialization
  RollbackState Event parentWorking)
variable (storageAddress : Address) (additional : Nat)
variable (doneOutcome : HostStorageDriver.Context
  RollbackState (FrameTrace Event) →
    Core.Value → Core.Store → FrameOutcome TrapReason)

example :
    (initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome).resumeWithFuel
        initialization inputs doneOutcome additional =
      initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs (fuel + additional) doneOutcome :=
  ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_resumeWithFuel
    initialization storageAddress inputs fuel additional doneOutcome

end Solcore.Test.CurrentAddressObservationProperties
end

section
-- leanmerge: from Solcore.Test.ExecutionEnvironmentSeal
/-! External regressions for the immutable nested-execution environment seal. -/

set_option autoImplicit false

namespace Tests.ExecutionEnvironmentSeal

open Solcore.Core
open Solcore.ContractRuntime
open Tests.OneLevelNestedExecutionFixture

private def root : CheckedCoreContract :=
  rootContract .commit childTargetWord

private def child : CheckedCoreContract :=
  childReturnContract

private def callRegistry : CheckedContractRegistry :=
  registry root child

private def templateId : Word := ⟨0xc1, by decide⟩

private def creationTemplate : CheckedCreationTemplate := {
  initializer := child
  runtime := child
}

private def creationTemplates : CheckedCreationTemplateRegistry := {
  lookup := fun identifier =>
    if identifier = templateId then some creationTemplate else none
}

private def createdAddress : Address := ⟨0xc2, by decide⟩

private def addressPolicy : CreationAddressPolicy := {
  derive := fun _creator _nonce => createdAddress
}

private def environment : ExecutionEnvironment := {
  callRegistry := callRegistry
  creationTemplates := creationTemplates
  creationAddressPolicy := addressPolicy
}

private def runWith (fuel : Nat) :
    OneLevelNestedExecution.Result (initialWorld root child) root invocation :=
  OneLevelNestedExecution.runWithEnvironment root invocation
    (installedRoot root child) environment fuel

private def runCallsOnly (fuel : Nat) :
    OneLevelNestedExecution.Result (initialWorld root child) root invocation :=
  OneLevelNestedExecution.run root invocation (installedRoot root child)
    callRegistry fuel

/-- The old public API is exactly the calls-only environment specialization. -/
example (fuel : Nat) :
    runCallsOnly fuel =
      OneLevelNestedExecution.runWithEnvironment root invocation
        (installedRoot root child) (.callsOnly callRegistry) fuel :=
  rfl

/-- OOF exposes the full retained environment, including creation capabilities. -/
private def outOfFuelRetainsFullEnvironment : Bool :=
  match (runWith 0).view with
  | .outOfFuel retained _mode _reachable =>
      (retained.creationTemplates.lookup templateId).isSome &&
        (retained.creationAddressPolicy.derive rootAddress Word.zero ==
          createdAddress) &&
        (retained.callRegistry.resolve?
          (initialWorld root child) childAddress).isSome
  | .completed _ => false

private theorem outOfFuelRetainsFullEnvironment_exact :
    outOfFuelRetainsFullEnvironment = true := by
  native_decide

/-- Resumption has no environment input and equals one run under the retained one. -/
example (additional : Nat) :
    OneLevelNestedExecution.resumeWithFuel (runWith 0) additional =
      runWith additional := by
  simpa [runWith] using
    OneLevelNestedExecution.resumeWithFuel_runWithEnvironment
      root invocation (installedRoot root child) environment 0 additional

private def resumedAndOneShotCompleteIdentically : Bool :=
  let resumed := OneLevelNestedExecution.resumeWithFuel (runWith 0) 512
  let oneShot := runWith 512
  match resumed.view, oneShot.view with
  | .completed left, .completed right =>
      left.outcome == right.outcome &&
        childStorageValue? left.finalWorld == childStorageValue? right.finalWorld
  | _, _ => false

private theorem resumedAndOneShotCompleteIdentically_exact :
    resumedAndOneShotCompleteIdentically = true := by
  native_decide

/-- Calls-only deliberately rejects the ADR-0148 root creation capability. -/
private def callsOnlyCreationIsUnavailable : Bool :=
  let creationRoot :=
    Tests.Adr0148CreationEndToEndFixture.commitRoot
  let result := OneLevelNestedExecution.run creationRoot
    Tests.Adr0148CreationEndToEndFixture.invocation
    Tests.Adr0148CreationEndToEndFixture.commitInstalled
    Tests.Adr0148CreationEndToEndFixture.environment.callRegistry 512
  match result.view with
  | .outOfFuel _ _ _ => false
  | .completed terminal =>
      terminal.outcome ==
        .trapped ContractCallFailure.unavailable.code &&
      terminal.finalWorld.nonce?
          Tests.Adr0148CreationEndToEndFixture.creator ==
        some Tests.Adr0148CreationEndToEndFixture.oldNonce &&
      (terminal.finalWorld.account?
        Tests.Adr0148CreationEndToEndFixture.created).isNone

private theorem callsOnlyCreationIsUnavailable_exact :
    callsOnlyCreationIsUnavailable = true := by
  native_decide

def runExecutionEnvironmentSealTests : IO Unit := do
  unless outOfFuelRetainsFullEnvironment do
    throw (IO.userError "OOF did not retain the full execution environment")
  unless resumedAndOneShotCompleteIdentically do
    throw (IO.userError "retained-environment resumption differed from one-shot")
  unless callsOnlyCreationIsUnavailable do
    throw (IO.userError "calls-only creation did not return unavailable")

end Tests.ExecutionEnvironmentSeal
end

section
-- leanmerge: from Solcore.Test.TopLevelExecutionFixture
/-! Checked program and explicit-state fixture for ADR-0145 top-level execution. -/

set_option autoImplicit false

namespace Tests.TopLevelExecutionFixture

open Solcore.Core
open Solcore.ContractRuntime

def targetAddress : Address := ⟨0x10, by decide⟩
def callerAddress : Address := ⟨0x20, by decide⟩
def otherAddress : Address := ⟨0x30, by decide⟩

def targetSlot : Word := ⟨0x51, by decide⟩
def oldValue : Word := ⟨0x52, by decide⟩
def writtenValue : Word := ⟨0x53, by decide⟩
def retainedSlot : Word := ⟨0x61, by decide⟩
def retainedValue : Word := ⟨0x62, by decide⟩
def otherSlot : Word := ⟨0x71, by decide⟩
def otherValue : Word := ⟨0x72, by decide⟩

def returnSelector : Word := Word.zero
def revertSelector : Word := ⟨1, by decide⟩
def trapSelector : Word := ⟨2, by decide⟩
def returnPayload : Word := ⟨0xa1, by decide⟩
def revertPayload : Word := ⟨0xb2, by decide⟩
def trapCode : Word := ⟨0xc3, by decide⟩

def inputData : HostStorageDriver.InputData := {
  bytes := [0x11, 0x22, 0x33].toByteArray
  size_lt_wordModulus := by decide
}

def returnedExpr (payload : Word) : Expr :=
  .inLeft (.sum .word .word) (.word payload)

def revertedExpr (payload : Word) : Expr :=
  .inRight .word (.inLeft .word (.word payload))

def trappedExpr (reason : Word) : Expr :=
  .inRight .word (.inRight .word (.word reason))

/-- Write storage, observe call value, and dynamically select the halt kind. -/
def program : Program := {
  resultType := .sum .word (.sum .word .word)
  body :=
    .letE
      (.apply
        (.var HostFunction.storageWrite.index)
        (.pair (.word targetSlot) (.word writtenValue)))
      (.letE
        (.apply (.var (HostFunction.callValue.index + 1)) .unit)
        (.ifE
          (.binary .wordEq (.var 0) (.word returnSelector))
          (returnedExpr returnPayload)
          (.ifE
            (.binary .wordEq (.var 0) (.word revertSelector))
            (revertedExpr revertPayload)
            (trappedExpr trapCode))))
}

theorem program_host_checked : program.checkHost = true := by
  decide

def code : CheckedHostCoreProgram :=
  ⟨program, program_host_checked⟩

def contract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 code rfl

def targetAccount : Account :=
  Account.empty
    |>.storageWrite targetSlot oldValue
    |>.storageWrite retainedSlot retainedValue
    |>.withCode code

def otherAccount : Account :=
  Account.empty.storageWrite otherSlot otherValue

def initialWorld : WorldState :=
  WorldState.empty
    |>.putAccount otherAddress otherAccount
    |>.putAccount targetAddress targetAccount

def installed :
    InstalledCheckedCoreContract initialWorld targetAddress contract := {
  account := targetAccount
  account_present := by
    exact WorldState.account?_putAccount_same
      (WorldState.empty.putAccount otherAddress otherAccount)
      targetAddress targetAccount
  code_present := by
    change targetAccount.code? = some code
    simp [targetAccount]
}

def invocationWith (selector : Word) : TopLevelInvocation := {
  target := targetAddress
  caller := callerAddress
  callValue := selector
  inputData := inputData
}

def returnedInvocation : TopLevelInvocation :=
  invocationWith returnSelector

def revertedInvocation : TopLevelInvocation :=
  invocationWith revertSelector

def trappedInvocation : TopLevelInvocation :=
  invocationWith trapSelector

def runWith (selector : Word) (fuel : Nat) :=
  TopLevelExecution.run contract (invocationWith selector) installed fuel

def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

def speculativeTargetValue
    (result : TopLevelTerminalResult initialWorld targetAddress) : Option Word :=
  storageValueAt? result.terminalContext.context.values.working.1
    targetAddress targetSlot

def finalTargetValue
    (result : TopLevelTerminalResult initialWorld targetAddress) : Option Word :=
  storageValueAt? result.finalWorld targetAddress targetSlot

def writeRequestFuel : Nat := 9
def postWriteFuel : Nat := 10
def callValueRequestFuel : Nat := 16
def postCallValueFuel : Nat := 17
def returnCompletionFuel : Nat := 28
def revertTrapCompletionFuel : Nat := 37

end Tests.TopLevelExecutionFixture
end

section
-- leanmerge: from Solcore.Test.Adr0147BalancedTopLevelExecutionFixture
/-! Actual checked-Core worlds for balance-aware top-level execution tests. -/

set_option autoImplicit false

namespace Tests.Adr0147BalancedTopLevelExecutionFixture

open Solcore.Core
open Solcore.ContractRuntime
open Tests.TopLevelExecutionFixture

def zero : Word := Word.zero
def one : Word := ⟨1, by decide⟩
def two : Word := ⟨2, by decide⟩
def three : Word := ⟨3, by decide⟩
def four : Word := ⟨4, by decide⟩
def five : Word := ⟨5, by decide⟩
def eight : Word := ⟨8, by decide⟩
def nine : Word := ⟨9, by decide⟩
def ten : Word := ⟨10, by decide⟩

/-- A minimal checker-accepted root that always returns the fixture payload. -/
def returningProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := returnedExpr returnPayload
}

theorem returningProgram_checked : returningProgram.checkHost = true := by
  rfl

def returningContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨returningProgram, returningProgram_checked⟩ rfl

def callerAccount (balance : Word) : Account :=
  Account.empty.withBalance balance

def targetAccountFor
    (root : CheckedCoreContract) (balance : Word) : Account :=
  (targetAccount.withCode root.code).withBalance balance

/-- A cross-account world retaining the original storage and unrelated account. -/
def worldWithBalances
    (root : CheckedCoreContract)
    (callerBalance targetBalance : Word) : WorldState :=
  WorldState.empty
    |>.putAccount otherAddress otherAccount
    |>.putAccount callerAddress (callerAccount callerBalance)
    |>.putAccount targetAddress (targetAccountFor root targetBalance)

def installedWithBalances
    (root : CheckedCoreContract)
    (callerBalance targetBalance : Word) :
    InstalledCheckedCoreContract
      (worldWithBalances root callerBalance targetBalance)
      targetAddress root := {
  account := targetAccountFor root targetBalance
  account_present := by rfl
  code_present := by rfl
}

/-- A world with installed target code but no ordinary external caller account. -/
def worldWithoutCaller
    (root : CheckedCoreContract)
    (targetBalance : Word) : WorldState :=
  WorldState.empty
    |>.putAccount otherAddress otherAccount
    |>.putAccount targetAddress (targetAccountFor root targetBalance)

def installedWithoutCaller
    (root : CheckedCoreContract)
    (targetBalance : Word) :
    InstalledCheckedCoreContract
      (worldWithoutCaller root targetBalance) targetAddress root := {
  account := targetAccountFor root targetBalance
  account_present := by rfl
  code_present := by rfl
}

def invocationFrom (caller : Address) (value : Word) : TopLevelInvocation := {
  target := targetAddress
  caller := caller
  callValue := value
  inputData := inputData
}

def emptyRegistry : CheckedContractRegistry := {
  lookup := fun _ => none
}

def runWithBalances
    (root : CheckedCoreContract)
    (callerBalance targetBalance value : Word)
    (fuel : Nat) :=
  BalancedTopLevelExecution.run root
    (invocationFrom callerAddress value)
    (installedWithBalances root callerBalance targetBalance)
    emptyRegistry fuel

def runWithoutCaller
    (root : CheckedCoreContract)
    (targetBalance : Word)
    (caller : Address)
    (value : Word)
    (fuel : Nat) :=
  BalancedTopLevelExecution.run root (invocationFrom caller value)
    (installedWithoutCaller root targetBalance) emptyRegistry fuel

def completionFuel : Nat := 128

end Tests.Adr0147BalancedTopLevelExecutionFixture
end

section
-- leanmerge: from Solcore.Test.Adr0147BalancedTopLevelExecution
/-! Runtime regressions for atomic balance-aware checked root execution. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open TopLevelExecutionFixture
open Adr0147BalancedTopLevelExecutionFixture

private inductive ObservedStatus where
  | rejected (failure : BalanceTransferFailure)
  | completed (outcome : FrameOutcome Word)
  deriving BEq

private def observedStatus
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation) :
    Option ObservedStatus :=
  match result.terminalStatus? with
  | none => none
  | some (.error failure) => some (.rejected failure)
  | some (.ok outcome) => some (.completed outcome)

private def finalBalance?
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation)
    (address : Address) : Option (Option Word) :=
  result.finalWorld?.map fun world => world.balance? address

private def committedBalanceChangesMatch
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation)
    (caller : Address)
    (callerChange targetChange : Option (Option Word × Option Word)) : Bool :=
  match result.committedWorld? with
  | none => false
  | some ⟨_, delta⟩ =>
      delta.balanceChange? caller == callerChange &&
        delta.balanceChange? targetAddress == targetChange

private def completedWorkingMatches
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation)
    (caller : Address)
    (callerBalance targetBalance : Option Word)
    (targetStorage : Option Word) : Bool :=
  match result.view with
  | .rejected _ => false
  | .execution execution =>
      match execution.view with
      | .outOfFuel _ _ _ => false
      | .completed terminal =>
          let working := terminal.terminalContext.context.values.working.1
          working.balance? caller == callerBalance &&
            working.balance? targetAddress == targetBalance &&
            storageValueAt? working targetAddress targetSlot == targetStorage

private def rejectedMatches
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation)
    (failure : BalanceTransferFailure)
    (caller target : Address)
    (callerBalance targetBalance : Option Word) : Bool :=
  match result.view with
  | .execution _ => false
  | .rejected rejected =>
      rejected.failure == failure &&
        observedStatus result == some (.rejected failure) &&
        rejected.finalWorld.balance? caller == callerBalance &&
        rejected.finalWorld.balance? target == targetBalance &&
        rejected.committedDelta.balanceChange? caller == none &&
        rejected.committedDelta.balanceChange? target == none

private def terminalObservation
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation) :
    Option
      (ObservedStatus × (Option Word × Option Word)) :=
  match observedStatus result, result.finalWorld? with
  | some status, some world =>
      some (status,
        (world.balance? callerAddress, world.balance? targetAddress))
  | _, _ => none

private def zeroAbsentCallerRun :=
  BalancedTopLevelExecution.run contract returnedInvocation installed
    emptyRegistry completionFuel

private def zeroValueKeepsLegacyExecution : Bool :=
  initialWorld.balance? callerAddress == none &&
    observedStatus zeroAbsentCallerRun ==
      some (.completed (.returned (encodeWordBytesBE returnPayload))) &&
    finalBalance? zeroAbsentCallerRun callerAddress == some none &&
    match zeroAbsentCallerRun.finalWorld? with
    | none => false
    | some finalWorld =>
        storageValueAt? finalWorld targetAddress targetSlot == some writtenValue

private def returnedRun :=
  runWithBalances returningContract ten three one completionFuel

private def nonzeroReturnCommitsTransfer : Bool :=
  observedStatus returnedRun ==
      some (.completed (.returned (encodeWordBytesBE returnPayload))) &&
    finalBalance? returnedRun callerAddress == some (some nine) &&
    finalBalance? returnedRun targetAddress == some (some four) &&
    committedBalanceChangesMatch returnedRun callerAddress
      (some (some ten, some nine)) (some (some three, some four))

private def revertedRun :=
  runWithBalances contract ten three one completionFuel

private def rootRevertRollsBackTransfer : Bool :=
  observedStatus revertedRun ==
      some (.completed (.reverted (encodeWordBytesBE revertPayload))) &&
    completedWorkingMatches revertedRun callerAddress
      (some nine) (some four) (some writtenValue) &&
    finalBalance? revertedRun callerAddress == some (some ten) &&
    finalBalance? revertedRun targetAddress == some (some three) &&
    committedBalanceChangesMatch revertedRun callerAddress none none &&
    match revertedRun.finalWorld? with
    | none => false
    | some finalWorld =>
        storageValueAt? finalWorld targetAddress targetSlot == some oldValue

private def trappedRun :=
  runWithBalances contract ten three two completionFuel

private def rootTrapRollsBackTransfer : Bool :=
  observedStatus trappedRun == some (.completed (.trapped trapCode)) &&
    completedWorkingMatches trappedRun callerAddress
      (some eight) (some five) (some writtenValue) &&
    finalBalance? trappedRun callerAddress == some (some ten) &&
    finalBalance? trappedRun targetAddress == some (some three) &&
    committedBalanceChangesMatch trappedRun callerAddress none none &&
    match trappedRun.finalWorld? with
    | none => false
    | some finalWorld =>
        storageValueAt? finalWorld targetAddress targetSlot == some oldValue

private def absentSenderRejected : Bool :=
  rejectedMatches
    (runWithoutCaller returningContract three callerAddress one completionFuel)
    .senderAbsent callerAddress targetAddress none (some three)

private def insufficientSenderRejected : Bool :=
  rejectedMatches
    (runWithBalances returningContract zero three one completionFuel)
    .insufficientBalance callerAddress targetAddress (some zero) (some three)

private def overflowingRecipientRejected : Bool :=
  rejectedMatches
    (runWithBalances returningContract ten Word.maximum one completionFuel)
    .recipientOverflow callerAddress targetAddress
    (some ten) (some Word.maximum)

private def fundedSelfCallIsBalanceIdentity : Bool :=
  let result :=
    runWithoutCaller returningContract three targetAddress one completionFuel
  observedStatus result ==
      some (.completed (.returned (encodeWordBytesBE returnPayload))) &&
    finalBalance? result targetAddress == some (some three) &&
    committedBalanceChangesMatch result targetAddress none none

private def unfundedSelfCallRejected : Bool :=
  rejectedMatches
    (runWithoutCaller returningContract zero targetAddress one completionFuel)
    .insufficientBalance targetAddress targetAddress (some zero) (some zero)

private def splitStart :=
  runWithBalances returningContract ten three one 0

private def resumed :=
  BalancedTopLevelExecution.resumeWithFuel splitStart completionFuel

private def oneShot :=
  runWithBalances returningContract ten three one completionFuel

private def zeroFuelRetainsSingleTransfer : Bool :=
  (observedStatus splitStart).isNone && splitStart.finalWorld?.isNone &&
    match splitStart.view with
    | .rejected _ => false
    | .execution execution =>
        match execution.view with
        | .completed _ => false
        | .outOfFuel _ (.root frame) _ =>
            let working := frame.context.context.values.working.1
            working.balance? callerAddress == some nine &&
              working.balance? targetAddress == some four
        | .outOfFuel _ (.child _) _ => false
        | .outOfFuel _ (.initializer _) _ => false

private def resumedMatchesOneShotWithoutDoubleTransfer : Bool :=
  terminalObservation resumed == terminalObservation oneShot &&
    terminalObservation resumed ==
      some (.completed (.returned (encodeWordBytesBE returnPayload)),
        (some nine, some four)) &&
    committedBalanceChangesMatch resumed callerAddress
      (some (some ten, some nine)) (some (some three, some four))

private def allScenarios : Bool :=
  zeroValueKeepsLegacyExecution &&
    nonzeroReturnCommitsTransfer &&
    rootRevertRollsBackTransfer &&
    rootTrapRollsBackTransfer &&
    absentSenderRejected &&
    insufficientSenderRejected &&
    overflowingRecipientRejected &&
    fundedSelfCallIsBalanceIdentity &&
    unfundedSelfCallRejected &&
    zeroFuelRetainsSingleTransfer &&
    resumedMatchesOneShotWithoutDoubleTransfer

private theorem compileTimeBalancedTopLevelScenarios :
    allScenarios = true := by
  native_decide

def testAdr0147BalancedTopLevelExecution : IO Unit := do
  assertTrue zeroValueKeepsLegacyExecution
    "zero call value did not preserve legacy execution with an absent caller"
  assertTrue nonzeroReturnCommitsTransfer
    "root return did not commit the exact preflight debit and credit"
  assertTrue rootRevertRollsBackTransfer
    "root revert did not roll balance and storage back to the initial world"
  assertTrue rootTrapRollsBackTransfer
    "root trap did not roll balance and storage back to the initial world"
  assertTrue absentSenderRejected
    "an absent sender was not rejected before Core execution"
  assertTrue insufficientSenderRejected
    "an insufficient sender balance was not rejected atomically"
  assertTrue overflowingRecipientRejected
    "recipient overflow was not rejected atomically"
  assertTrue fundedSelfCallIsBalanceIdentity
    "a funded self-call changed its account balance"
  assertTrue unfundedSelfCallRejected
    "an unfunded self-call bypassed the sufficient-balance check"
  assertTrue zeroFuelRetainsSingleTransfer
    "fuel zero did not retain exactly one prepared balance transfer"
  assertTrue resumedMatchesOneShotWithoutDoubleTransfer
    "resumption differed from one-shot execution or repeated the transfer"

end Tests
end

section
-- leanmerge: from Solcore.Test.Adr0148ExecutionEnvironment
/-! External and executable checks for the immutable creation environment. -/

set_option autoImplicit false

namespace Tests.Adr0148ExecutionEnvironment

open Solcore.Core
open Solcore.ContractRuntime
open Tests.TopLevelExecutionFixture

example := CheckedCreationTemplate.mk_initializer
example := CheckedCreationTemplate.mk_runtime
example := CheckedCreationTemplateRegistry.empty_lookup
example := ExecutionEnvironment.callsOnly_callRegistry
example := ExecutionEnvironment.callsOnly_creationTemplates_lookup
example := ExecutionEnvironment.inertCreationAddressPolicy_derive
example := ExecutionEnvironment.callsOnly_creationAddressPolicy_derive

private def identifier : Word := ⟨0x48, by decide⟩
private def otherIdentifier : Word := ⟨0x49, by decide⟩
private def template : CheckedCreationTemplate := {
  initializer := contract
  runtime := contract
}

private def templates : CheckedCreationTemplateRegistry := {
  lookup := fun selected => if selected = identifier then some template else none
}

private def calls : CheckedContractRegistry := {
  lookup := fun address => if address = targetAddress then some contract else none
}

private def templateLookupExact : Bool :=
  match templates.lookup identifier with
  | none => false
  | some selected =>
      selected.initializer.code.program == program &&
        selected.runtime.code.program == program &&
        (templates.lookup otherIdentifier).isNone

private def emptyAndCallsOnlyExact : Bool :=
  (CheckedCreationTemplateRegistry.empty.lookup identifier).isNone &&
    ((ExecutionEnvironment.callsOnly calls).creationTemplates.lookup
      identifier).isNone &&
    match (ExecutionEnvironment.callsOnly calls).callRegistry.lookup
        targetAddress with
    | none => false
    | some selected =>
        selected.code.program == program &&
          (ExecutionEnvironment.callsOnly calls).creationAddressPolicy.derive
            callerAddress identifier == ⟨0, by decide⟩

private theorem compileTimeEnvironmentExact :
    templateLookupExact && emptyAndCallsOnlyExact = true := by
  native_decide

def testAdr0148ExecutionEnvironment : IO Unit := do
  unless templateLookupExact do
    throw (IO.userError "checked creation template lookup changed")
  unless emptyAndCallsOnlyExact do
    throw (IO.userError "calls-only execution environment was not inert")

end Tests.Adr0148ExecutionEnvironment
end

section
-- leanmerge: from Solcore.Test.BalancedExecutionEnvironment
/-! Actual fixed-environment regressions at the balanced top-level boundary. -/

set_option autoImplicit false

namespace Tests.BalancedExecutionEnvironment

open Solcore.Core
open Solcore.ContractRuntime
open Tests.Adr0147BalancedTopLevelExecutionFixture
open Tests.TopLevelExecutionFixture

private def templateId : Word := ⟨0xd1, by decide⟩
private def createdAddress : Address := ⟨0xd2, by decide⟩

private def environment : ExecutionEnvironment := {
  callRegistry := emptyRegistry
  creationTemplates := {
    lookup := fun identifier =>
      if identifier = templateId then
        some { initializer := returningContract, runtime := returningContract }
      else none
  }
  creationAddressPolicy := {
    derive := fun _creator _nonce => createdAddress
  }
}

private def invocation : TopLevelInvocation :=
  invocationFrom callerAddress one

private def runWith (fuel : Nat) :=
  BalancedTopLevelExecution.runWithEnvironment returningContract invocation
    (installedWithBalances returningContract ten three) environment fuel

private def exhaustedRetainsEnvironmentAndOneTransfer : Bool :=
  match (runWith 0).view with
  | .rejected _ => false
  | .execution execution =>
      match execution.view with
      | .completed _ => false
      | .outOfFuel retained (.root frame) _ =>
          (retained.creationTemplates.lookup templateId).isSome &&
            retained.creationAddressPolicy.derive callerAddress Word.zero ==
              createdAddress &&
            frame.context.context.values.working.1.balance? callerAddress ==
              some nine &&
            frame.context.context.values.working.1.balance? targetAddress ==
              some four
      | .outOfFuel _ (.child _) _ => false
      | .outOfFuel _ (.initializer _) _ => false

private def terminalBalances
    (result : BalancedTopLevelExecution.Result
      (worldWithBalances returningContract ten three)
      returningContract invocation) : Option (Option Word × Option Word) :=
  result.finalWorld?.map fun world =>
    (world.balance? callerAddress, world.balance? targetAddress)

private def resumedUsesRetainedEnvironmentWithoutRepeatingTransfer : Bool :=
  let resumed := BalancedTopLevelExecution.resumeWithFuel (runWith 0) completionFuel
  let oneShot := runWith completionFuel
  terminalBalances resumed == terminalBalances oneShot &&
    terminalBalances resumed == some (some nine, some four)

private theorem exhaustedRetainsEnvironmentAndOneTransfer_exact :
    exhaustedRetainsEnvironmentAndOneTransfer = true := by
  native_decide

private theorem resumedUsesRetainedEnvironmentWithoutRepeatingTransfer_exact :
    resumedUsesRetainedEnvironmentWithoutRepeatingTransfer = true := by
  native_decide

example (additional : Nat) :
    BalancedTopLevelExecution.resumeWithFuel (runWith 0) additional =
      runWith additional := by
  simpa [runWith] using
    BalancedTopLevelExecution.resumeWithFuel_runWithEnvironment
      returningContract invocation
      (installedWithBalances returningContract ten three)
      environment 0 additional

def runBalancedExecutionEnvironmentTests : IO Unit := do
  unless exhaustedRetainsEnvironmentAndOneTransfer do
    throw (IO.userError "balanced OOF lost its environment or repeated transfer")
  unless resumedUsesRetainedEnvironmentWithoutRepeatingTransfer do
    throw (IO.userError "balanced retained-environment resume differed from one-shot")

end Tests.BalancedExecutionEnvironment
end

section
-- leanmerge: from Solcore.Test.TopLevelExecution
/-! Executable end-to-end regressions for ADR-0145 top-level finalization. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open TopLevelExecutionFixture

private def codeMatches
    (state : WorldState) (address : Address) : Bool :=
  match state.code? address with
  | some selected => selected.program == program
  | none => false

private def testWriteBoundaries : IO Unit := do
  match runWith returnSelector writeRequestFuel with
  | .outOfFuel context _ _ _ delta _ =>
      assertTrue
        (storageValueAt? context.context.values.working.1
          targetAddress targetSlot == some oldValue)
        "fuel 9 must stop before applying the target storage write"
      assertTrue (delta.slotChange? targetSlot == none)
        "the pre-write speculative delta must be empty"
  | .completed _ =>
      throw (IO.userError "fuel 9 must not complete top-level execution")

  match runWith returnSelector postWriteFuel with
  | .outOfFuel context _ _ _ delta _ =>
      assertTrue
        (storageValueAt? context.context.values.working.1
          targetAddress targetSlot == some writtenValue)
        "fuel 10 must retain the applied speculative storage write"
      assertTrue
        (delta.slotChange? targetSlot == some (oldValue, writtenValue))
        "the post-write speculative delta must expose the exact old/new pair"
  | .completed _ =>
      throw (IO.userError "fuel 10 must remain resumable")

private def testReturnedCommit : IO Unit := do
  match runWith returnSelector (returnCompletionFuel - 1) with
  | .outOfFuel _ _ _ _ _ _ => pure ()
  | .completed _ =>
      throw (IO.userError "return must not complete one fuel unit early")

  match runWith returnSelector returnCompletionFuel with
  | .outOfFuel _ _ _ _ _ _ =>
      throw (IO.userError "return must complete at its measured boundary")
  | .completed result =>
      assertTrue
        (result.outcome == .returned (encodeWordBytesBE returnPayload))
        "the executed left injection must decode as canonical return data"
      assertTrue
        (result.coreValue ==
          .inLeft (.sum .word .word) (.word returnPayload))
        "return must retain the exact dynamic Core value"
      assertTrue (result.coreStore == [])
        "the fixture must retain its exact empty Core-local Store"
      assertTrue (speculativeTargetValue result == some writtenValue)
        "return must retain the speculative storage write"
      assertTrue (finalTargetValue result == some writtenValue)
        "return must commit the terminal working WorldState"
      assertTrue
        (result.committedDelta.slotChange? targetSlot ==
          some (oldValue, writtenValue))
        "return must report the committed target-slot change"
      assertTrue
        (storageValueAt? result.finalWorld targetAddress retainedSlot ==
          some retainedValue)
        "return must preserve an untouched target slot"
      assertTrue
        (storageValueAt? result.finalWorld otherAddress otherSlot ==
          some otherValue)
        "return must preserve a distinct Account"
      assertTrue (codeMatches result.finalWorld targetAddress)
        "return must preserve the installed target code"

private def testCallValueBoundaries : IO Unit := do
  match runWith returnSelector callValueRequestFuel with
  | .outOfFuel context state _ _ delta _ =>
      assertTrue
        (storageValueAt? context.context.values.working.1
          targetAddress targetSlot == some writtenValue)
        "fuel 16 must retain the earlier storage write"
      assertTrue
        (match hostAdvance state with
          | .suspended suspension => suspension.request == .callValue
          | _ => false)
        "fuel 16 must stop at the call-value request"
      assertTrue
        (delta.slotChange? targetSlot == some (oldValue, writtenValue))
        "call-value suspension must retain the speculative delta"
  | .completed _ =>
      throw (IO.userError "fuel 16 must remain resumable")

  match runWith returnSelector postCallValueFuel with
  | .outOfFuel _ state _ _ _ _ =>
      assertTrue (state.control == .ret (.word returnSelector))
        "fuel 17 must have injected the exact call value"
  | .completed _ =>
      throw (IO.userError "fuel 17 must remain resumable")

private def testRevertedRollback : IO Unit := do
  match runWith revertSelector (revertTrapCompletionFuel - 1) with
  | .outOfFuel _ _ _ _ _ _ => pure ()
  | .completed _ =>
      throw (IO.userError "revert must not complete one fuel unit early")

  match runWith revertSelector revertTrapCompletionFuel with
  | .outOfFuel _ _ _ _ _ _ =>
      throw (IO.userError "revert must complete at its measured boundary")
  | .completed result =>
      assertTrue
        (result.outcome == .reverted (encodeWordBytesBE revertPayload))
        "the executed nested-left injection must decode as revert data"
      assertTrue (speculativeTargetValue result == some writtenValue)
        "revert must retain evidence that the speculative write occurred"
      assertTrue (finalTargetValue result == some oldValue)
        "revert must select the explicit initial WorldState"
      assertTrue (result.committedDelta.slotChange? targetSlot == none)
        "revert must expose no committed target-slot change"
      assertTrue
        (result.workingDelta.slotChange? targetSlot ==
          some (oldValue, writtenValue))
        "revert must keep its pre-rollback working delta observable"
      assertTrue (codeMatches result.finalWorld targetAddress)
        "revert rollback must retain the installed target code"

private def testTrappedRollback : IO Unit := do
  match runWith trapSelector (revertTrapCompletionFuel - 1) with
  | .outOfFuel _ _ _ _ _ _ => pure ()
  | .completed _ =>
      throw (IO.userError "trap must not complete one fuel unit early")

  match runWith trapSelector revertTrapCompletionFuel with
  | .outOfFuel _ _ _ _ _ _ =>
      throw (IO.userError "trap must complete at its measured boundary")
  | .completed result =>
      assertTrue (result.outcome == .trapped trapCode)
        "the executed nested-right injection must retain its exact trap code"
      assertTrue (speculativeTargetValue result == some writtenValue)
        "trap must retain evidence that the speculative write occurred"
      assertTrue (finalTargetValue result == some oldValue)
        "trap must select the explicit initial WorldState"
      assertTrue (result.committedDelta.slotChange? targetSlot == none)
        "trap must expose no committed target-slot change"
      assertTrue
        (result.workingDelta.slotChange? targetSlot ==
          some (oldValue, writtenValue))
        "trap must keep its pre-rollback working delta observable"
      assertTrue
        (storageValueAt? result.finalWorld otherAddress otherSlot ==
          some otherValue)
        "trap rollback must preserve a distinct Account"

private def testDirectInputs : IO Unit := do
  let invocation := invocationWith revertSelector
  let inputs := invocation.executionInputs
  assertTrue (inputs.codeAddress == targetAddress)
    "direct-call code address must equal the target"
  assertTrue (inputs.currentAddress == targetAddress)
    "direct-call current address must equal the target"
  assertTrue (inputs.callerAddress == callerAddress)
    "direct-call caller must remain explicit"
  assertTrue (inputs.callValue == revertSelector)
    "direct-call value must remain explicit"
  assertTrue (inputs.inputData.bytes == inputData.bytes)
    "direct-call input bytes must remain explicit"

private def expectReturned
    (execution :
      TopLevelRunResult initialWorld contract returnedInvocation)
    (message : String) : IO Unit := do
  match execution with
  | .outOfFuel _ _ _ _ _ _ => throw (IO.userError message)
  | .completed result =>
      assertTrue
        (result.outcome == .returned (encodeWordBytesBE returnPayload) &&
          finalTargetValue result == some writtenValue)
        message

private def testResumption : IO Unit := do
  expectReturned
    (TopLevelExecution.resumeWithFuel
      (runWith returnSelector writeRequestFuel)
      (returnCompletionFuel - writeRequestFuel))
    "fuel split 9+19 must reach the exact returned commit"
  expectReturned
    (TopLevelExecution.resumeWithFuel
      (runWith returnSelector postWriteFuel)
      (returnCompletionFuel - postWriteFuel))
    "fuel split 10+18 must reach the exact returned commit"

  match TopLevelExecution.resumeWithFuel
      (runWith revertSelector writeRequestFuel)
      (revertTrapCompletionFuel - writeRequestFuel) with
  | .outOfFuel _ _ _ _ _ _ =>
      throw (IO.userError "fuel split 9+28 must complete revert")
  | .completed result =>
      assertTrue
        (result.outcome == .reverted (encodeWordBytesBE revertPayload) &&
          finalTargetValue result == some oldValue &&
          result.committedDelta.slotChange? targetSlot == none)
        "resumed revert must roll back the speculative write"

  match TopLevelExecution.resumeWithFuel
      (runWith trapSelector postWriteFuel)
      (revertTrapCompletionFuel - postWriteFuel) with
  | .outOfFuel _ _ _ _ _ _ =>
      throw (IO.userError "fuel split 10+27 must complete trap")
  | .completed result =>
      assertTrue
        (result.outcome == .trapped trapCode &&
          finalTargetValue result == some oldValue &&
          result.committedDelta.slotChange? targetSlot == none)
        "resumed trap must roll back the speculative write"

  expectReturned
    (TopLevelExecution.resumeWithFuel
      (runWith returnSelector returnCompletionFuel) 64)
    "a completed top-level return must remain terminal"

def testTopLevelExecution : IO Unit := do
  testWriteBoundaries
  testCallValueBoundaries
  testReturnedCommit
  testRevertedRollback
  testTrappedRollback
  testDirectInputs
  testResumption

end Tests
end

section
-- leanmerge: from Solcore.Test.TopLevelObservationFixture
/-! Read-only checked program observing every direct top-level address/input role. -/

set_option autoImplicit false

namespace Tests.TopLevelObservationFixture

open Solcore.Core
open Solcore.ContractRuntime

def targetAddress : Address := ⟨0x10, by decide⟩
def alternateTargetAddress : Address := ⟨0x11, by decide⟩
def callerAddress : Address := ⟨0x20, by decide⟩
def alternateCallerAddress : Address := ⟨0x21, by decide⟩
def otherAddress : Address := ⟨0x30, by decide⟩

def retainedSlot : Word := ⟨0x51, by decide⟩
def retainedValue : Word := ⟨0x52, by decide⟩
def otherSlot : Word := ⟨0x61, by decide⟩
def otherValue : Word := ⟨0x62, by decide⟩
def observedOffset : Word := ⟨1, by decide⟩
def missingByteResult : Word := ⟨0xee, by decide⟩
def callerWeight : Word := ⟨1, by decide⟩
def sizeWeight : Word := ⟨3, by decide⟩
def byteWeight : Word := ⟨5, by decide⟩
def codeWeight : Word := ⟨7, by decide⟩
def currentWeight : Word := ⟨11, by decide⟩
def storageWeight : Word := ⟨13, by decide⟩

def inputData : HostStorageDriver.InputData := {
  bytes := [0xa5, 0x7f, 0x01].toByteArray
  size_lt_wordModulus := by decide
}

/-- Same size as `inputData`, with only the observed byte changed. -/
def differentByteInputData : HostStorageDriver.InputData := {
  bytes := [0xa5, 0x80, 0x01].toByteArray
  size_lt_wordModulus := by decide
}

/-- Same observed byte as `inputData`, with only the size changed. -/
def differentSizeInputData : HostStorageDriver.InputData := {
  bytes := [0xa5, 0x7f, 0x01, 0x02].toByteArray
  size_lt_wordModulus := by decide
}

def missingByteInputData : HostStorageDriver.InputData := {
  bytes := [0xa5].toByteArray
  size_lt_wordModulus := by decide
}

private def addObservations
    (caller size byte code current storage : Expr) : Expr :=
  .binary .wordAdd
    (.binary .wordAdd
      (.binary .wordAdd
        (.binary .wordAdd
          (.binary .wordAdd
            (.binary .wordMul caller (.word callerWeight))
            (.binary .wordMul size (.word sizeWeight)))
          (.binary .wordMul byte (.word byteWeight)))
        (.binary .wordMul code (.word codeWeight)))
      (.binary .wordMul current (.word currentWeight)))
    (.binary .wordMul storage (.word storageWeight))

/-
After the sixth `let`, the retained observations have these indexes inside the
right `caseE` branch: byte 0, storage 1, current 2, code 3, size 5, caller 6.
-/
def observedResultExpr : Expr :=
  .caseE (.var 3)
    (.word missingByteResult)
    (addObservations
      (.var 6) (.var 5) (.var 0) (.var 3) (.var 2) (.var 1))

/-!
Observe caller, input size, one optional input byte, and all three direct-call
target roles. The program performs no storage write and returns their modular
weighted sum, or `missingByteResult` when the byte is absent. Distinct weights
separate caller, size, byte, and target variation. In a direct call the three
target roles intentionally have the same value; their individual derivation
laws complement this runtime observation.
-/
def program : Program := {
  resultType := .word
  body :=
    .letE
      (.apply (.var HostFunction.callerAddress.index) .unit)
      (.letE
        (.apply (.var (HostFunction.inputDataSize.index + 1)) .unit)
        (.letE
          (.apply
            (.var (HostFunction.inputDataByte?.index + 2))
            (.word observedOffset))
          (.letE
            (.apply (.var (HostFunction.codeAddress.index + 3)) .unit)
            (.letE
              (.apply (.var (HostFunction.currentAddress.index + 4)) .unit)
              (.letE
                (.apply
                  (.var (HostFunction.storageAddress.index + 5)) .unit)
                observedResultExpr)))))
}

theorem program_host_checked : program.checkHost = true := by
  decide

def code : CheckedHostCoreProgram :=
  ⟨program, program_host_checked⟩

def wordCode : CheckedHostCoreWordProgram :=
  ⟨code, rfl⟩

def contract : CheckedCoreContract :=
  CheckedCoreContract.returnWord wordCode

def targetAccount : Account :=
  Account.empty
    |>.storageWrite retainedSlot retainedValue
    |>.withCode contract.code

def otherAccount : Account :=
  Account.empty.storageWrite otherSlot otherValue

/-- Install the same checked contract at one caller-selected direct target. -/
def worldAt (target : Address) : WorldState :=
  WorldState.empty
    |>.putAccount otherAddress otherAccount
    |>.putAccount target targetAccount

def installedAt (target : Address) :
    InstalledCheckedCoreContract (worldAt target) target contract := {
  account := targetAccount
  account_present := by
    exact WorldState.account?_putAccount_same
      (WorldState.empty.putAccount otherAddress otherAccount)
      target targetAccount
  code_present := by
    change targetAccount.code? = some contract.code
    simp [targetAccount]
}

def invocationAt
    (target caller : Address)
    (input : HostStorageDriver.InputData) : TopLevelInvocation := {
  target := target
  caller := caller
  callValue := Word.zero
  inputData := input
}

def checksum
    (target caller : Address)
    (size byte : Word) : Word :=
  let total := (addressToWord caller).mul callerWeight
  let total := total.add (size.mul sizeWeight)
  let total := total.add (byte.mul byteWeight)
  let total := total.add ((addressToWord target).mul codeWeight)
  let total := total.add ((addressToWord target).mul currentWeight)
  total.add ((addressToWord target).mul storageWeight)

def expectedResult
    (target caller : Address)
    (input : HostStorageDriver.InputData) : Word :=
  match input.byte? observedOffset with
  | none => missingByteResult
  | some byte => checksum target caller input.sizeWord byte

def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

def completionFuel : Nat := 256

end Tests.TopLevelObservationFixture
end

section
-- leanmerge: from Solcore.Test.TopLevelObservation
/-! Runtime regressions for read-only direct top-level input observations. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open TopLevelObservationFixture

private def codeMatches_variant
    (state : WorldState) (target : Address) : Bool :=
  match state.code? target with
  | some selected => selected.program == program
  | none => false

private def assertObservation
    (runTarget runCaller : Address)
    (runInput : HostStorageDriver.InputData)
    (label : String) : IO Unit := do
  let invocation := invocationAt runTarget runCaller runInput
  let inputs := invocation.executionInputs
  let installed := installedAt runTarget
  let initialWorld := worldAt runTarget
  let expected := expectedResult runTarget runCaller runInput

  assertTrue (inputs.codeAddress == runTarget)
    s!"{label}: code address was not derived from the direct target"
  assertTrue (inputs.currentAddress == runTarget)
    s!"{label}: current address was not derived from the direct target"
  assertTrue
    ((TopLevelExecution.initialContext installed).context.storageAddress ==
      runTarget)
    s!"{label}: storage address was not derived from the direct target"
  assertTrue (inputs.callerAddress == runCaller)
    s!"{label}: caller address was not retained"
  assertTrue (inputs.inputData.sizeWord == runInput.sizeWord)
    s!"{label}: input size was not retained"
  assertTrue
    (inputs.inputData.byte? observedOffset == runInput.byte? observedOffset)
    s!"{label}: optional input byte was not retained"

  match TopLevelExecution.run contract invocation installed completionFuel with
  | .outOfFuel _ _ _ _ _ _ =>
      throw (IO.userError s!"{label}: read-only observation did not complete")
  | .completed result =>
      assertTrue (result.coreValue == .word expected)
        s!"{label}: Core did not return the exact observation checksum"
      assertTrue (result.coreStore == [])
        s!"{label}: the read-only fixture changed the Core-local Store"
      assertTrue
        (result.outcome == .returned (encodeWordBytesBE expected))
        s!"{label}: the checksum did not become canonical return bytes"
      assertTrue
        (result.workingDelta.slotChange? retainedSlot == none)
        s!"{label}: read-only execution reported a speculative storage change"
      assertTrue
        (result.committedDelta.slotChange? retainedSlot == none)
        s!"{label}: read-only return reported a committed storage change"
      assertTrue
        (storageValueAt? result.terminalContext.context.values.working.1
            runTarget retainedSlot == some retainedValue)
        s!"{label}: speculative execution changed retained target storage"
      assertTrue
        (storageValueAt? result.finalWorld runTarget retainedSlot ==
          some retainedValue)
        s!"{label}: return changed retained target storage"
      assertTrue
        (storageValueAt? result.finalWorld otherAddress otherSlot ==
          some otherValue)
        s!"{label}: return changed a distinct Account"
      assertTrue (codeMatches_variant result.finalWorld runTarget)
        s!"{label}: return changed the installed checked code"
      assertTrue
        (storageValueAt? initialWorld runTarget retainedSlot ==
          storageValueAt? result.finalWorld runTarget retainedSlot)
        s!"{label}: final target observation differs from the initial world"

def testTopLevelObservation : IO Unit := do
  assertTrue program.checkHost
    "the host checker rejected the read-only observation program"

  let baseline := expectedResult targetAddress callerAddress inputData
  let callerVariant :=
    expectedResult targetAddress alternateCallerAddress inputData
  let byteVariant :=
    expectedResult targetAddress callerAddress differentByteInputData
  let sizeVariant :=
    expectedResult targetAddress callerAddress differentSizeInputData
  let targetVariant :=
    expectedResult alternateTargetAddress callerAddress inputData

  assertTrue
    (baseline != callerVariant && baseline != byteVariant &&
      baseline != sizeVariant && baseline != targetVariant &&
      callerVariant != byteVariant && callerVariant != sizeVariant &&
      callerVariant != targetVariant && byteVariant != sizeVariant &&
      byteVariant != targetVariant && sizeVariant != targetVariant)
    "fixture sentinels do not distinguish caller, byte, size, and target"
  assertTrue
    (expectedResult targetAddress callerAddress missingByteInputData ==
      missingByteResult)
    "missing optional input byte did not select its explicit result"

  assertObservation targetAddress callerAddress inputData "baseline"
  assertObservation targetAddress alternateCallerAddress inputData
    "alternate caller"
  assertObservation targetAddress callerAddress differentByteInputData
    "alternate input byte"
  assertObservation targetAddress callerAddress differentSizeInputData
    "alternate input size"
  assertObservation alternateTargetAddress callerAddress inputData
    "alternate direct target"
  assertObservation targetAddress callerAddress missingByteInputData
    "missing input byte"

end Tests
end
