import Solcore.Test.SelectedCheckedWordExecutionFixture

/-! Executable branch, fuel, and returned-frame regressions for ADR-0143. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open ParentIndexedSelectedExecutionFixture
open CheckedHostCoreWordProgramExecutionFixture
open SelectedCheckedWordExecutionFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def absentRunDoesNotRun
    (execution : Execution absentContext) (expectedFuel : Nat) : Bool :=
  execution.providedFuel == expectedFuel &&
    execution.execution?.isNone && execution.completion?.isNone &&
    match execution.selection with
    | .codeAbsent => true
    | _ => false

private def nonWordRunDoesNotRun
    (execution : Execution nonWordContext) (expectedFuel : Nat) : Bool :=
  execution.providedFuel == expectedFuel &&
    execution.execution?.isNone && execution.completion?.isNone &&
    match execution.selection with
    | .nonWord selected _ => selected.program == boolProgram
    | _ => false

private def exactExhaustionAt
    (fuel : Nat) (expectedStorage : Word)
    (stateMatches : State → Bool) : Bool :=
  let execution := wordExecution fuel
  execution.completion?.isNone &&
    match execution.selection, execution.execution? with
    | .word selected,
        some (retained, ⟨finalContext, .outOfFuel exhausted⟩) =>
        selected.code.program == program &&
          retained.code.program == program &&
          contextHasTarget finalContext expectedStorage &&
          contextPreserved finalContext && stateMatches exhausted
    | _, _ => false

private def exactReturnedResolution
    (completion : WordReturnedFrameCompletion Nat (FrameTrace Nat)) : Bool :=
  let frame : FrameContinuationContext Nat (FrameTrace Nat) TrapReason :=
    completion.toFrameContinuationContext
  completion.word == inputData.sizeWord &&
    completion.store == [] &&
    completion.returnData == canonicalInputSizeReturnData &&
    completion.returnData.size == 32 &&
    decodeWordBytesBE? completion.returnData == some inputData.sizeWord &&
    contextHasTarget completion.context writtenValue &&
    contextPreserved completion.context &&
    match frame.resolve with
    | .returned state effects data =>
        storageValueAt? state storageAddress targetSlot == some writtenValue &&
          effects.rollback == 201 && effects.trace.toList == [] &&
          data == completion.returnData
    | _ => false

private def exactCompletionAt (fuel : Nat) : Bool :=
  let execution := wordExecution fuel
  match execution.selection, execution.execution?, execution.completion? with
  | .word selected,
      some (retained, ⟨finalContext, .done (.word result) store⟩),
      some completion =>
      selected.code.program == program && retained.code.program == program &&
        result == inputData.sizeWord && store == [] &&
        completion.context.readStorage targetSlot == finalContext.readStorage targetSlot &&
        exactReturnedResolution completion
  | _, _, _ => false

private def sameCompletion
    (left right : Option
      (WordReturnedFrameCompletion Nat (FrameTrace Nat))) : Bool :=
  match left, right with
  | some left, some right =>
      left.word == right.word && left.store == right.store &&
        left.returnData == right.returnData &&
        contextHasTarget left.context writtenValue &&
        contextHasTarget right.context writtenValue &&
        contextPreserved left.context && contextPreserved right.context
  | _, _ => false

private theorem split_9_7_exact :
    (wordExecution writeRequestFuel).resumeWithFuel 7 =
      wordExecution completionFuel := by
  simpa [wordExecution, writeRequestFuel, completionFuel] using
    SelectedCheckedWordExecution.start_resumeWithFuel
      context executionInputs writeRequestFuel 7

private theorem split_10_6_exact :
    (wordExecution postWriteFuel).resumeWithFuel 6 =
      wordExecution completionFuel := by
  simpa [wordExecution, postWriteFuel, completionFuel] using
    SelectedCheckedWordExecution.start_resumeWithFuel
      context executionInputs postWriteFuel 6

private theorem split_15_1_exact :
    (wordExecution inputRequestFuel).resumeWithFuel 1 =
      wordExecution completionFuel := by
  simpa [wordExecution, inputRequestFuel, completionFuel] using
    SelectedCheckedWordExecution.start_resumeWithFuel
      context executionInputs inputRequestFuel 1

def testSelectedCheckedWordExecution : IO Unit := do
  assertTrue
    (absentRunDoesNotRun (absentExecution 0) 0 &&
      absentRunDoesNotRun ((absentExecution 0).resumeWithFuel 0) 0 &&
      absentRunDoesNotRun (absentExecution 64) 64 &&
      absentRunDoesNotRun
        ((absentExecution 0).resumeWithFuel 64) 64)
    "codeAbsent selection unexpectedly executed"

  assertTrue
    (nonWordRunDoesNotRun (nonWordExecution 0) 0 &&
      nonWordRunDoesNotRun ((nonWordExecution 0).resumeWithFuel 0) 0 &&
      nonWordRunDoesNotRun (nonWordExecution 64) 64 &&
      nonWordRunDoesNotRun
        ((nonWordExecution 0).resumeWithFuel 64) 64)
    "nonWord selection unexpectedly executed or lost its checked code"

  assertTrue
    (exactExhaustionAt writeRequestFuel oldValue writeRequestReady &&
      exactExhaustionAt postWriteFuel writtenValue beforeInputSuffix &&
      exactExhaustionAt inputRequestFuel writtenValue inputSizeRequestReady)
    "a measured Word exhaustion boundary lost its exact retained run"

  assertTrue (exactCompletionAt completionFuel)
    "fuel 16 did not retain the exact canonical selected Word completion"

  let completion := (wordExecution completionFuel).completion?
  let split9 :=
    ((wordExecution writeRequestFuel).resumeWithFuel 7).completion?
  let split10 :=
    ((wordExecution postWriteFuel).resumeWithFuel 6).completion?
  let split15 :=
    ((wordExecution inputRequestFuel).resumeWithFuel 1).completion?
  let terminal :=
    ((wordExecution completionFuel).resumeWithFuel 48).completion?
  let zero :=
    ((wordExecution completionFuel).resumeWithFuel 0).completion?
  let added :=
    (((wordExecution writeRequestFuel).resumeWithFuel 3)
      |>.resumeWithFuel 4).completion?
  let combined :=
    ((wordExecution writeRequestFuel).resumeWithFuel (3 + 4)).completion?
  assertTrue
    (sameCompletion split9 completion &&
      sameCompletion split10 completion &&
      sameCompletion split15 completion &&
      sameCompletion terminal completion &&
      sameCompletion zero completion &&
      sameCompletion added combined && sameCompletion combined completion &&
      ((wordExecution completionFuel).resumeWithFuel 48).providedFuel == 64)
    "split, summed, or terminal resumption changed the selected completion"

  have _ := split_9_7_exact
  have _ := split_10_6_exact
  have _ := split_15_1_exact
  pure ()

end Tests
