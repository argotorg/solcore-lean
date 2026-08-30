import Solcore.Test.CheckedHostCoreWordProgramExecutionFixture

/-! Executable regressions for checked Word completion and canonical returns. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open ParentIndexedSelectedExecutionFixture
open CheckedHostCoreWordProgramExecutionFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def boolProgram : Program := {
  resultType := .bool
  body := .bool true
}

private theorem boolProgram_host_checked : boolProgram.checkHost = true := by
  decide

private def boolCode : CheckedHostCoreProgram :=
  ⟨boolProgram, boolProgram_host_checked⟩

private def rejectedWordProgram : Program := {
  resultType := .word
  body := .bool true
}

private def initialResult :=
  wordCode.runWithStorage context executionInputs writeRequestFuel

private def completionAt (fuel : Nat) :=
  wordCode.runWithStorageReturnedFrameCompletion?
    context executionInputs fuel

private def postWriteResult :=
  wordCode.runWithStorage context executionInputs postWriteFuel

private def resumedCompletion :=
  ((wordCode.runWithStorage context executionInputs writeRequestFuel)
    |>.resumeWithFuel
      (@HostStorageDriver.handler Nat (FrameTrace Nat) executionInputs) 7)
    |>.toWordReturnedFrameCompletion?

private def postWriteResumedCompletion :=
  (postWriteResult.resumeWithFuel
      (@HostStorageDriver.handler Nat (FrameTrace Nat) executionInputs) 6)
    |>.toWordReturnedFrameCompletion?

private theorem resumedCompletion_exact :
    resumedCompletion = completionAt completionFuel := by
  simpa [resumedCompletion, completionAt, writeRequestFuel,
    completionFuel] using
    wordCode.toWordReturnedFrameCompletion?_resumeWithFuel_runWithStorage
      context executionInputs writeRequestFuel 7

private theorem postWriteResumedCompletion_exact :
    postWriteResumedCompletion = completionAt completionFuel := by
  simpa [postWriteResumedCompletion, postWriteResult, completionAt,
    postWriteFuel, completionFuel] using
    wordCode.toWordReturnedFrameCompletion?_resumeWithFuel_runWithStorage
      context executionInputs postWriteFuel 6

private def exactReturnedResolution
    (completion : WordReturnedFrameCompletion Nat (FrameTrace Nat))
    (expectedStorage expectedWord : Word)
    (expectedStore : Store) : Bool :=
  let frame : FrameContinuationContext Nat (FrameTrace Nat)
      ParentIndexedSelectedExecutionFixture.TrapReason :=
    completion.toFrameContinuationContext
  completion.word == expectedWord &&
    completion.store == expectedStore &&
    completion.returnData.size == 32 &&
    decodeWordBytesBE? completion.returnData == some expectedWord &&
    contextHasTarget completion.context expectedStorage &&
    contextPreserved completion.context &&
    match frame.resolve with
    | .returned state effects data =>
        storageValueAt? state storageAddress targetSlot ==
            some expectedStorage &&
          effects.rollback == 201 && effects.trace.toList == [] &&
          data == completion.returnData
    | _ => false

private def sameCompletionObservations
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

private def arbitraryUnitProjectionIsNone : Bool :=
  let result : HostDriverResult
      (HostStorageDriver.Context Nat (FrameTrace Nat)) :=
    ⟨context, .done .unit []⟩
  result.toWordReturnedFrameCompletion?.isNone

private def syntheticFrameBridgeIsCanonical (word : Word) : Bool :=
  exactReturnedResolution
    ⟨context, word, [.unit]⟩ oldValue word [.unit]

private def storeIndependentReturn
    (completion : WordReturnedFrameCompletion Nat (FrameTrace Nat)) : Bool :=
  let withoutStore : WordReturnedFrameCompletion Nat (FrameTrace Nat) :=
    ⟨completion.context, completion.word, []⟩
  let left : FrameContinuationContext Nat (FrameTrace Nat)
      ParentIndexedSelectedExecutionFixture.TrapReason :=
    completion.toFrameContinuationContext
  let right : FrameContinuationContext Nat (FrameTrace Nat)
      ParentIndexedSelectedExecutionFixture.TrapReason :=
    withoutStore.toFrameContinuationContext
  match left.resolve, right.resolve with
  | .returned leftState leftEffects leftData,
      .returned rightState rightEffects rightData =>
      storageValueAt? leftState storageAddress targetSlot ==
          storageValueAt? rightState storageAddress targetSlot &&
        leftEffects.rollback == rightEffects.rollback &&
        leftEffects.trace.toList == rightEffects.trace.toList &&
        leftData == rightData
  | _, _ => false

def testCheckedHostCoreWordProgramExecution : IO Unit := do
  match CheckedHostCoreWordProgram.ofChecked? code,
      CheckedHostCoreWordProgram.ofProgram? program with
  | some checked, some checkedFromProgram =>
      assertTrue
        (checked.code.program.resultType == .word &&
          checkedFromProgram.code.program.resultType == .word)
        "Word admission did not retain the exact checked program"
  | _, _ =>
      throw (IO.userError "a checked Word program was rejected")

  assertTrue
    ((CheckedHostCoreWordProgram.ofChecked? boolCode).isNone &&
      (CheckedHostCoreWordProgram.ofProgram? rejectedWordProgram).isNone &&
      arbitraryUnitProjectionIsNone)
    "a non-Word or unchecked result received an invented Word return"

  match initialResult with
  | ⟨exhaustedContext, .outOfFuel exhausted⟩ =>
      assertTrue
        (contextHasTarget exhaustedContext oldValue &&
          contextPreserved exhaustedContext &&
          writeRequestReady exhausted &&
          (completionAt writeRequestFuel).isNone)
        "fuel 9 was not retained as exact pre-write exhaustion"
  | _ =>
      throw (IO.userError "fuel 9 unexpectedly completed or faulted")

  match postWriteResult with
  | ⟨exhaustedContext, .outOfFuel exhausted⟩ =>
      assertTrue
        (contextHasTarget exhaustedContext writtenValue &&
          contextPreserved exhaustedContext &&
          beforeInputSuffix exhausted && !writeRequestReady exhausted &&
          (completionAt postWriteFuel).isNone)
        "fuel 10 did not retain the exact post-write continuation"
  | _ =>
      throw (IO.userError "fuel 10 unexpectedly completed or faulted")

  match wordCode.runWithStorage context executionInputs inputRequestFuel with
  | ⟨exhaustedContext, .outOfFuel exhausted⟩ =>
      assertTrue
        (contextHasTarget exhaustedContext writtenValue &&
          contextPreserved exhaustedContext &&
          inputSizeRequestReady exhausted &&
          (completionAt inputRequestFuel).isNone)
        "fuel 15 was not retained at the exact input-size request"
  | _ =>
      throw (IO.userError "fuel 15 unexpectedly completed or faulted")

  match completionAt completionFuel with
  | none =>
      throw (IO.userError "fuel 16 did not project a Word completion")
  | some completion =>
      assertTrue
        (exactReturnedResolution completion writtenValue inputData.sizeWord [] &&
          completion.returnData == canonicalInputSizeReturnData)
        "fuel 16 did not produce the exact canonical returned frame"

  assertTrue
    (sameCompletionObservations resumedCompletion
      (completionAt completionFuel) &&
      sameCompletionObservations postWriteResumedCompletion
        (completionAt completionFuel) &&
      sameCompletionObservations (completionAt 64)
        (completionAt completionFuel))
    "split or larger fuel changed the completed Word observation"

  assertTrue
    (syntheticFrameBridgeIsCanonical Word.zero &&
      syntheticFrameBridgeIsCanonical cellWord &&
      syntheticFrameBridgeIsCanonical Word.maximum)
    "zero, nontrivial, or maximum Word failed the canonical frame bridge"

  match cellCode.runWithStorageReturnedFrameCompletion?
      context executionInputs 6 with
  | none =>
      throw (IO.userError "the cell-bearing Word program did not complete")
  | some completion =>
      assertTrue
        (exactReturnedResolution completion oldValue cellWord [.bool true] &&
          storeIndependentReturn completion)
        "Core Store was lost or serialized into the returned Word bytes"

end Tests
