import Solcore.Semantics.ParentIndexedSelectedExecutionSessionFoldProperties
import Solcore.Test.ParentIndexedSelectedExecutionFixture

/-! Executable regressions for proof-refined selected execution sessions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open ParentIndexedSelectedExecutionFixture

namespace ParentIndexedSelectedExecutionSessionTest

private abbrev Session := ParentIndexedSelectedExecutionSession
  Nat Nat TrapReason parentWorking

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def startWith
    (selectedInitialization :
      ParentIndexedFrameInitialization Nat Nat parentWorking)
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome TrapReason)
    (fuel : Nat) : Session :=
  ParentIndexedSelectedExecutionSession.start selectedInitialization
    storageAddress executionInputs doneOutcome fuel

private def startReturned (fuel : Nat) : Session :=
  startWith initialization returnedDoneOutcome fuel

private theorem wholeSessionZero :
    (startReturned writeRequestFuel).resumeWithFuel 0 =
      startReturned writeRequestFuel := by
  exact ParentIndexedSelectedExecutionSession.resumeWithFuel_zero _

private theorem postWriteWholeExact :
    (startReturned writeRequestFuel).resumeWithFuel 1 =
      startReturned postWriteFuel := by
  simpa [startReturned, startWith, writeRequestFuel, postWriteFuel] using
    (ParentIndexedSelectedExecutionSession.start_resumeWithFuel
      initialization storageAddress executionInputs returnedDoneOutcome 9 1)

private theorem inputRequestWholeExact :
    ((startReturned writeRequestFuel).resumeWithFuel 1).resumeWithFuel 5 =
      startReturned inputRequestFuel := by
  rw [ParentIndexedSelectedExecutionSession.resumeWithFuel_add]
  simpa [startReturned, startWith, writeRequestFuel, inputRequestFuel] using
    (ParentIndexedSelectedExecutionSession.start_resumeWithFuel
      initialization storageAddress executionInputs returnedDoneOutcome 9 6)

private theorem directCompletionWholeExact :
    (startReturned writeRequestFuel).resumeWithFuel 7 =
      startReturned completionFuel := by
  simpa [startReturned, startWith, writeRequestFuel, completionFuel] using
    (ParentIndexedSelectedExecutionSession.start_resumeWithFuel
      initialization storageAddress executionInputs returnedDoneOutcome 9 7)

private theorem sequentialCompletionWholeExact :
    ((startReturned writeRequestFuel).resumeWithFuel 1).resumeWithFuel 6 =
      startReturned completionFuel := by
  rw [ParentIndexedSelectedExecutionSession.resumeWithFuel_add]
  exact directCompletionWholeExact

private theorem completedResultIdentity
    (session : Session)
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (value : Value) (store : Store)
    (continuation : ParentIndexedFrameContinuationContext
      Nat Nat TrapReason parentWorking)
    (completed :
      session.result = .completed context value store continuation)
    (additional : Nat) :
    (session.resumeWithFuel additional).result = session.result := by
  rw [ParentIndexedSelectedExecutionSession.resumeWithFuel_result, completed]
  rfl

private def exactExhaustion
    (session : Session) (expected : Word)
    (stateCheck : State → Bool) : Bool :=
  match session.result with
  | .outOfFuel context state =>
      contextHasTarget context expected && contextPreserved context &&
        stateCheck state
  | _ => false

private def postWriteWithoutReplay (state : State) : Bool :=
  beforeInputSuffix state && !writeRequestReady state

private def sameExhaustion
    (left right : Session) (expected : Word)
    (stateCheck : State → Bool) : Bool :=
  match left.result, right.result with
  | .outOfFuel leftContext leftState,
      .outOfFuel rightContext rightState =>
      contextHasTarget leftContext expected &&
        contextHasTarget rightContext expected &&
        contextPreserved leftContext && contextPreserved rightContext &&
        leftState == rightState && stateCheck leftState && stateCheck rightState
  | _, _ => false

private def exactCompletion
    (session : Session) (expected : FoldMarker) : Bool :=
  match session.result with
  | .completed context value store continuation =>
      contextHasTarget context writtenValue && contextPreserved context &&
        ParentIndexedSelectedExecutionFixture.exactCompletion value store &&
        foldResult continuation == expected
  | _ => false

private def sameCompletion
    (left right : Session) (expected : FoldMarker) : Bool :=
  match left.result, right.result with
  | .completed leftContext leftValue leftStore leftContinuation,
      .completed rightContext rightValue rightStore rightContinuation =>
      contextHasTarget leftContext writtenValue &&
        contextHasTarget rightContext writtenValue &&
        contextPreserved leftContext && contextPreserved rightContext &&
        leftValue == rightValue && leftStore == rightStore &&
        ParentIndexedSelectedExecutionFixture.exactCompletion
          leftValue leftStore &&
        ParentIndexedSelectedExecutionFixture.exactCompletion
          rightValue rightStore &&
        foldResult leftContinuation == expected &&
        foldResult rightContinuation == expected
  | _, _ => false

private def resultIsStorageAbsent (session : Session) : Bool :=
  match session.result with
  | .storageAbsent => true
  | _ => false

private def resultIsCodeAbsent (session : Session) : Bool :=
  match session.result with
  | .codeAbsent => true
  | _ => false

def testParentIndexedSelectedExecutionSession : IO Unit := do
  assertTrue program.checkHost
    "the host checker rejected the selected-session fixture"

  let missingStorage :=
    startWith missingStorageInitialization returnedDoneOutcome completionFuel
  let missingCode :=
    startWith missingCodeInitialization returnedDoneOutcome completionFuel
  assertTrue
    (resultIsStorageAbsent missingStorage && resultIsCodeAbsent missingCode)
    "session start did not preserve distinct storage/code absence branches"

  let initial := startReturned writeRequestFuel
  assertTrue
    (initial.providedFuel == 9 &&
      exactExhaustion initial oldValue writeRequestReady)
    "fuel 9 did not retain the exact pre-write request and old context"

  let zero := initial.resumeWithFuel 0
  have _zeroExact : zero = initial := wholeSessionZero
  assertTrue
    (zero.providedFuel == 9 &&
      sameExhaustion zero initial oldValue writeRequestReady)
    "zero fuel changed the whole selected execution session"

  let postWrite := initial.resumeWithFuel 1
  let postWriteOneShot := startReturned postWriteFuel
  have _postWriteExact : postWrite = postWriteOneShot := postWriteWholeExact
  assertTrue
    (postWrite.providedFuel == 10 &&
      exactExhaustion postWrite writtenValue postWriteWithoutReplay &&
      sameExhaustion postWrite postWriteOneShot
        writtenValue postWriteWithoutReplay)
    "9+1 did not match one-shot 10 after exactly one storage write"

  let inputRequest := postWrite.resumeWithFuel 5
  let inputRequestOneShot := startReturned inputRequestFuel
  have _inputExact : inputRequest = inputRequestOneShot :=
    inputRequestWholeExact
  assertTrue
    (inputRequest.providedFuel == 15 &&
      exactExhaustion inputRequest writtenValue inputSizeRequestReady &&
      sameExhaustion inputRequest inputRequestOneShot
        writtenValue inputSizeRequestReady)
    "9+1+5 did not match one-shot 15 at the input-size request"

  let directCompletion := initial.resumeWithFuel 7
  let sequentialCompletion := postWrite.resumeWithFuel 6
  let completionOneShot := startReturned completionFuel
  have _directExact : directCompletion = completionOneShot :=
    directCompletionWholeExact
  have _sequentialExact : sequentialCompletion = completionOneShot :=
    sequentialCompletionWholeExact
  assertTrue
    (directCompletion.providedFuel == 16 &&
      sequentialCompletion.providedFuel == 16 &&
      exactCompletion completionOneShot .returned &&
      sameCompletion directCompletion completionOneShot .returned &&
      sameCompletion sequentialCompletion completionOneShot .returned)
    "direct 9+7 or sequential 9+1+6 differed from one-shot 16"

  match completedEq : completionOneShot.result with
  | .completed context value store continuation =>
      let terminal := completionOneShot.resumeWithFuel 100
      have _resultExact : terminal.result = completionOneShot.result :=
        completedResultIdentity completionOneShot context value store
          continuation completedEq 100
      assertTrue
        (terminal.providedFuel == 116 &&
          sameCompletion terminal completionOneShot .returned)
        "terminal resumption changed the result or failed to advance its budget"
  | _ =>
      throw (IO.userError "one-shot fuel 16 did not complete")

end ParentIndexedSelectedExecutionSessionTest

export ParentIndexedSelectedExecutionSessionTest
  (testParentIndexedSelectedExecutionSession)

end Tests
