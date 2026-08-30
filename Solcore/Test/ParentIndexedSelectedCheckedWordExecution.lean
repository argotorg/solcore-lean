import Solcore.Test.ParentIndexedSelectedCheckedWordExecutionFixture

/-! Executable provenance, fuel, and parent-return regressions for ADR-0144. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open ParentIndexedSelectedExecutionFixture
open CheckedHostCoreWordProgramExecutionFixture
open SelectedCheckedWordExecutionFixture
open ParentIndexedSelectedCheckedWordExecutionFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def codeAbsentPresent (fuel : Nat) : Bool :=
  match codeAbsentExecution? fuel with
  | some entry =>
      entry.execution.execution?.isNone &&
        entry.execution.completion?.isNone &&
        (entry.returnedCompletion? (TrapReason := TrapReason)).isNone &&
        match entry.execution.selection with
        | .codeAbsent => true
        | _ => false
  | none => false

private def nonWordPresent (fuel : Nat) : Bool :=
  match nonWordExecution? fuel with
  | some entry =>
      entry.execution.execution?.isNone &&
        entry.execution.completion?.isNone &&
        (entry.returnedCompletion? (TrapReason := TrapReason)).isNone &&
        match entry.execution.selection with
        | .nonWord selected _ => selected.program == boolProgram
        | _ => false
  | none => false

private def exactExhaustionAt
    (fuel : Nat) (expectedStorage : Word)
    (stateMatches : State → Bool) : Bool :=
  match wordExecution? fuel with
  | some entry =>
      entry.execution.completion?.isNone &&
        (entry.returnedCompletion? (TrapReason := TrapReason)).isNone &&
        match entry.execution.selection, entry.execution.execution? with
        | .word selected,
            some (retained, ⟨finalContext, .outOfFuel exhausted⟩) =>
            selected.code.program == program &&
              retained.code.program == program &&
              contextHasTarget finalContext expectedStorage &&
              contextPreserved finalContext && stateMatches exhausted
        | _, _ => false
  | none => false

private def exactReturnedPair (fuel : Nat) : Bool :=
  match wordExecution? fuel with
  | none => false
  | some entry =>
      match entry.returnedCompletion? (TrapReason := TrapReason) with
      | none => false
      | some (completion, continuation) =>
          completion.word == inputData.sizeWord && completion.store == [] &&
            completion.returnData == canonicalInputSizeReturnData &&
            completion.returnData.size == 32 &&
            decodeWordBytesBE? completion.returnData == some inputData.sizeWord &&
            contextHasTarget completion.context writtenValue &&
            contextPreserved completion.context &&
            storageValueAt? continuation.stateCheckpoint
                storageAddress targetSlot == some oldValue &&
            continuation.effectCheckpoint.rollback == 101 &&
            continuation.effectCheckpoint.trace.toList == [] &&
            continuation.effectWorking.rollback == 201 &&
            continuation.effectWorking.trace.toList == [] &&
            match continuation.resolve with
            | .returned state effects data =>
                storageValueAt? state storageAddress targetSlot ==
                    some writtenValue &&
                  effects.rollback == 201 && effects.trace.toList == [] &&
                  data == canonicalInputSizeReturnData
            | _ => false

private def sameReturnedPair
    (left right : Option
      (WordReturnedFrameCompletion Nat (FrameTrace Nat) ×
        ParentIndexedFrameContinuationContext
          Nat Nat TrapReason parentWorking)) : Bool :=
  match left, right with
  | some (leftCompletion, leftContinuation),
      some (rightCompletion, rightContinuation) =>
      leftCompletion.word == rightCompletion.word &&
        leftCompletion.store == rightCompletion.store &&
        leftCompletion.returnData == rightCompletion.returnData &&
        contextHasTarget leftCompletion.context writtenValue &&
        contextHasTarget rightCompletion.context writtenValue &&
        leftContinuation.effectCheckpoint.rollback ==
          rightContinuation.effectCheckpoint.rollback &&
        leftContinuation.effectWorking.rollback ==
          rightContinuation.effectWorking.rollback
  | _, _ => false

private def splitPair? (fuel additional : Nat) :=
  (wordExecution? fuel).bind fun entry =>
    (entry.resumeWithFuel additional).returnedCompletion?
      (TrapReason := TrapReason)

private def legacyCanonicalCompletion : Bool :=
  match wordExecution? completionFuel with
  | none => false
  | some entry =>
      match entry.returnedCompletion? (TrapReason := TrapReason) with
      | none => false
      | some (completion, continuation) =>
          match initialization.runCodeWithStorageParentIndexedResult
              storageAddress executionInputs completionFuel
              canonicalWordDoneOutcome with
          | .completed finalContext (.word word) store legacyContinuation =>
              word == completion.word && store == completion.store &&
                finalContext.readStorage targetSlot ==
                  completion.context.readStorage targetSlot &&
                legacyContinuation.effectCheckpoint.rollback ==
                  continuation.effectCheckpoint.rollback &&
                legacyContinuation.effectWorking.rollback ==
                  continuation.effectWorking.rollback &&
                match legacyContinuation.resolve, continuation.resolve with
                | .returned leftState _ leftData,
                    .returned rightState _ rightData =>
                    storageValueAt? leftState storageAddress targetSlot ==
                        storageValueAt? rightState storageAddress targetSlot &&
                      leftData == rightData
                | _, _ => false
          | _ => false

def testParentIndexedSelectedCheckedWordExecution : IO Unit := do
  assertTrue
    ((missingStorageExecution? 0).isNone &&
      (missingStorageExecution? 64).isNone &&
      ((missingStorageExecution? 0).map
        (fun entry => entry.resumeWithFuel 64)).isNone)
    "storage absence did not remain the unique outer none branch"

  assertTrue
    (codeAbsentPresent 0 && codeAbsentPresent 64 &&
      nonWordPresent 0 && nonWordPresent 64)
    "a present non-executing code branch was flattened or executed"

  assertTrue
    (exactExhaustionAt writeRequestFuel oldValue writeRequestReady &&
      exactExhaustionAt postWriteFuel writtenValue beforeInputSuffix &&
      exactExhaustionAt inputRequestFuel writtenValue inputSizeRequestReady)
    "a measured parent Word exhaustion boundary lost its retained state"

  assertTrue (exactReturnedPair completionFuel)
    "fuel 16 did not produce the exact canonical returned parent pair"

  let completed := (wordExecution? completionFuel).bind fun entry =>
    entry.returnedCompletion? (TrapReason := TrapReason)
  assertTrue
    (sameReturnedPair (splitPair? writeRequestFuel 7) completed &&
      sameReturnedPair (splitPair? postWriteFuel 6) completed &&
      sameReturnedPair (splitPair? inputRequestFuel 1) completed &&
      sameReturnedPair (splitPair? completionFuel 48) completed &&
      sameReturnedPair (splitPair? completionFuel 0) completed &&
      sameReturnedPair (splitPair? writeRequestFuel (3 + 4))
        ((wordExecution? writeRequestFuel).bind fun entry =>
          ((entry.resumeWithFuel 3).resumeWithFuel 4).returnedCompletion?
            (TrapReason := TrapReason)))
    "split, zero, addition, or terminal parent resumption changed completion"

  assertTrue legacyCanonicalCompletion
    "conditional generic parent coherence lost canonical Word completion"

end Tests
