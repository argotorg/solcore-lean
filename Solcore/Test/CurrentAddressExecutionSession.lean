import Solcore.ContractRuntime.ParentIndexedSelectedExecution
import Solcore.Test.CurrentAddressExecutionFixture

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
