import Solcore.Test.ParentIndexedSelectedExecutionFixture

/-! Runtime fold observations for branch-complete selected execution. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open ParentIndexedSelectedExecutionFixture

namespace ParentIndexedSelectedExecutionFold

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def failBranch (label phase : String) : IO Unit :=
  throw (IO.userError s!"{label}: expected completed {phase}")

/-- Check one completion policy before and after terminal resumption. -/
private def checkPolicy
    (label : String)
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome TrapReason)
    (expected : FoldMarker) : IO Unit := do
  let completed := runWith doneOutcome completionFuel
  match completed with
  | .completed context value store continuation =>
      assertTrue (exactCompletion value store)
        s!"{label}: completion payload changed"
      assertTrue (contextHasTarget context writtenValue)
        s!"{label}: completed working storage did not keep the write"
      assertTrue (contextPreserved context)
        s!"{label}: completed checkpoint or effects changed"
      assertTrue (foldResult continuation == expected)
        s!"{label}: existing fold selected the wrong branch or payload"

      let resumed :=
        ParentIndexedSelectedExecutionResult.resumeWithFuel
          (.completed context value store continuation : Result)
          initialization executionInputs doneOutcome 100
      match resumedEq : resumed with
      | .completed resumedContext resumedValue resumedStore
          resumedContinuation =>
          have exactResume :
              resumed = (.completed context value store continuation :
                Result) := by
            exact ParentIndexedSelectedExecutionResult.resumeWithFuel_completed
              context value store continuation
              initialization executionInputs doneOutcome 100
          have payloadEq :
              (.completed resumedContext resumedValue resumedStore
                  resumedContinuation : Result) =
                .completed context value store continuation :=
            resumedEq.symm.trans exactResume
          have _samePayload :
              resumedContext = context ∧ resumedValue = value ∧
                resumedStore = store ∧
                  resumedContinuation = continuation := by
            cases payloadEq
            exact ⟨rfl, rfl, rfl, rfl⟩
          assertTrue (exactCompletion resumedValue resumedStore)
            s!"{label}: resumed completion payload changed"
          assertTrue (resumedValue == value && resumedStore == store)
            s!"{label}: terminal resumption changed value or local store"
          assertTrue
            (contextHasTarget resumedContext writtenValue)
            s!"{label}: resumed working storage changed"
          assertTrue (contextPreserved resumedContext)
            s!"{label}: resumed checkpoint or effects changed"
          assertTrue (foldResult resumedContinuation == expected)
            s!"{label}: terminal resumption changed the fold observation"
      | _ => failBranch label "resumption"
  | _ => failBranch label "execution"

/-- Return, revert, and trap policies retain exact fold observations. -/
def testParentIndexedSelectedExecutionFold : IO Unit := do
  checkPolicy "returned" returnedDoneOutcome .returned
  checkPolicy "reverted" revertedDoneOutcome .reverted
  checkPolicy "trapped" trappedDoneOutcome .trapped

end ParentIndexedSelectedExecutionFold

export ParentIndexedSelectedExecutionFold
  (testParentIndexedSelectedExecutionFold)

end Tests
