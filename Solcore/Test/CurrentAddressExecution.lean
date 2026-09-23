import Solcore.Test.CurrentAddressExecutionFixture

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
