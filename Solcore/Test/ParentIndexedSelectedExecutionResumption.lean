import Solcore.Test.ParentIndexedSelectedExecutionFixture

/-! Executable regressions for branch-complete parent resumption. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open ParentIndexedSelectedExecutionFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def resume
    (result : Result) (additional : Nat) : Result :=
  result.resumeWithFuel
    initialization executionInputs returnedDoneOutcome additional

private theorem resume_fault_exact
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (state : State) :
    resume (.fault context syntheticFault state) 100 =
      .fault context syntheticFault state := by
  rfl

private theorem resume_completed_exact
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (value : Value) (store : Store)
    (continuation : ParentIndexedFrameContinuationContext
      Nat Nat TrapReason parentWorking) :
    resume (.completed context value store continuation) 100 =
      .completed context value store continuation := by
  rfl

private def firstResult : Result :=
  runWith returnedDoneOutcome writeRequestFuel

private def postWriteSplit : Result := resume firstResult 1
private def inputRequestSplit : Result := resume firstResult 6
private def completionSplit : Result := resume firstResult 7
private def sequentialSplit : Result := resume postWriteSplit 6
private def zeroSplit : Result := resume firstResult 0
private def completedResumed : Result := resume completionSplit 100

private def postWriteOneShot : Result :=
  runWith returnedDoneOutcome postWriteFuel

private def inputRequestOneShot : Result :=
  runWith returnedDoneOutcome inputRequestFuel

private def completionOneShot : Result :=
  runWith returnedDoneOutcome completionFuel

private def sameExhausted
    (left right : Result) (expectedValue : Word)
    (stateCheck : State → Bool) : Bool :=
  match left, right with
  | .outOfFuel leftContext leftState,
      .outOfFuel rightContext rightState =>
      contextHasTarget leftContext expectedValue &&
        contextHasTarget rightContext expectedValue &&
        contextPreserved leftContext && contextPreserved rightContext &&
        leftState == rightState && stateCheck leftState && stateCheck rightState
  | _, _ => false

private def sameCompletion (left right : Result) : Bool :=
  match left, right with
  | .completed leftContext leftValue leftStore leftContinuation,
      .completed rightContext rightValue rightStore rightContinuation =>
      contextHasTarget leftContext writtenValue &&
        contextHasTarget rightContext writtenValue &&
        contextPreserved leftContext && contextPreserved rightContext &&
        leftValue == rightValue && leftStore == rightStore &&
        exactCompletion leftValue leftStore &&
        exactCompletion rightValue rightStore &&
        foldResult leftContinuation == foldResult rightContinuation
  | _, _ => false

private def missingStorageResult : Result :=
  missingStorageInitialization.runCodeWithStorageParentIndexedResult
    storageAddress executionInputs completionFuel returnedDoneOutcome

private def missingCodeResult : Result :=
  missingCodeInitialization.runCodeWithStorageParentIndexedResult
    storageAddress executionInputs completionFuel returnedDoneOutcome

private def legacyIsStorageAbsent (result : Result) : Bool :=
  match result.toLegacy with
  | none => true
  | _ => false

private def legacyIsCodeAbsent (result : Result) : Bool :=
  match result.toLegacy with
  | some none => true
  | _ => false

private def exactInitialExhaustion (result : Result) : Bool :=
  match result with
  | .outOfFuel context state =>
      contextHasTarget context oldValue && contextPreserved context &&
        writeRequestReady state
  | _ => false

private def exactPostWriteExhaustion (result : Result) : Bool :=
  match result with
  | .outOfFuel context state =>
      contextHasTarget context writtenValue && contextPreserved context &&
        beforeInputSuffix state && !writeRequestReady state
  | _ => false

private def exactInputRequestExhaustion (result : Result) : Bool :=
  match result with
  | .outOfFuel context state =>
      contextHasTarget context writtenValue && contextPreserved context &&
        inputSizeRequestReady state
  | _ => false

private def exactReturnedCompletion (result : Result) : Bool :=
  match result with
  | .completed context value store continuation =>
      contextHasTarget context writtenValue && contextPreserved context &&
        exactCompletion value store && foldResult continuation == .returned
  | _ => false

private def syntheticFaultIdentity (context :
    HostStorageDriver.Context Nat (FrameTrace Nat)) (state : State) : Bool :=
  let faulted : Result := .fault context syntheticFault state
  match resume faulted 100 with
  | .fault resumedContext error resumedState =>
      error == syntheticFault && resumedState == state &&
        contextHasTarget resumedContext oldValue &&
        contextPreserved resumedContext
  | _ => false

def testParentIndexedSelectedExecutionResumption : IO Unit := do
  assertTrue program.checkHost
    "the host checker rejected the shared resumption fixture"

  match missingStorageResult, missingCodeResult with
  | .storageAbsent, .codeAbsent =>
      assertTrue
        (legacyIsStorageAbsent missingStorageResult &&
          legacyIsCodeAbsent missingCodeResult)
        "absence branches did not preserve their distinct legacy layers"
      match resume missingStorageResult 100, resume missingCodeResult 100 with
      | .storageAbsent, .codeAbsent => pure ()
      | _, _ =>
          throw (IO.userError "resumption changed an absence branch")
  | _, _ =>
      throw (IO.userError "storage and code absence were not distinct")

  assertTrue (exactInitialExhaustion firstResult)
    "fuel 9 did not retain the exact pre-write request and old context"

  assertTrue
    (exactPostWriteExhaustion postWriteSplit &&
      sameExhausted postWriteSplit postWriteOneShot
        writtenValue beforeInputSuffix)
    "9+1 did not match fuel 10 after handling the write exactly once"

  assertTrue
    (exactInputRequestExhaustion inputRequestSplit &&
      sameExhausted inputRequestSplit inputRequestOneShot
        writtenValue inputSizeRequestReady)
    "9+6 did not match fuel 15 at the retained input-size request"

  assertTrue
    (exactReturnedCompletion completionSplit &&
      sameCompletion completionSplit completionOneShot)
    "9+7 did not match the observable one-shot fuel-16 completion"

  match firstResult with
  | .outOfFuel context state =>
      assertTrue (syntheticFaultIdentity context state)
        "a synthetic raw fault was not an exact terminal identity"
  | _ =>
      throw (IO.userError "the fault identity fixture was not exhausted")

  assertTrue
    (sameExhausted zeroSplit firstResult oldValue writeRequestReady)
    "zero additional fuel changed an actual run result"

  assertTrue
    (exactReturnedCompletion sequentialSplit &&
      sameCompletion sequentialSplit completionSplit)
    "sequential additions +1 then +6 differed from the summed +7"

  assertTrue
    (exactReturnedCompletion completedResumed &&
      sameCompletion completedResumed completionSplit)
    "resuming an actual completed carrier changed its terminal observations"

end Tests
