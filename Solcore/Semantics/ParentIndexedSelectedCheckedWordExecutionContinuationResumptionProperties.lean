import Solcore.Semantics.ParentIndexedSelectedCheckedWordExecutionContinuationCoherenceProperties
import Solcore.Semantics.ParentIndexedSelectedCheckedWordExecutionResumptionProperties

/-! Terminal parent-return stability under additional fuel. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution

universe u v w

/-- Resumption rebuilds the same parent continuation from retained completion. -/
theorem toReturnedContinuation_resumeWithFuel
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.resumeWithFuel additional).toReturnedContinuation
        (TrapReason := TrapReason) completion
        (entry.completion?_resumeWithFuel_of_some
          additional completion completed) =
      entry.toReturnedContinuation completion completed :=
  rfl

/-- A successful completion/parent pair is terminal under more fuel. -/
theorem returnedCompletion?_resumeWithFuel_of_completion
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.resumeWithFuel additional).returnedCompletion?
        (TrapReason := TrapReason) =
      some (completion, entry.toReturnedContinuation completion completed) := by
  have resumed := entry.completion?_resumeWithFuel_of_some
    additional completion completed
  rw [(entry.resumeWithFuel additional).returnedCompletion?_of_completion
    (TrapReason := TrapReason) completion resumed]
  rw [entry.toReturnedContinuation_resumeWithFuel
    (TrapReason := TrapReason) additional completion completed]

/-- Once successful, the complete optional pair is unchanged by more fuel. -/
theorem returnedCompletion?_resumeWithFuel_stable
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.resumeWithFuel additional).returnedCompletion?
        (TrapReason := TrapReason) =
      entry.returnedCompletion? (TrapReason := TrapReason) := by
  rw [entry.returnedCompletion?_resumeWithFuel_of_completion
    (TrapReason := TrapReason) additional completion completed]
  rw [entry.returnedCompletion?_of_completion
    (TrapReason := TrapReason) completion completed]

/-- The derived continuation-only view is likewise terminal. -/
theorem returnedContinuation?_resumeWithFuel_stable
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.resumeWithFuel additional).returnedContinuation?
        (TrapReason := TrapReason) =
      entry.returnedContinuation? (TrapReason := TrapReason) := by
  unfold returnedContinuation?
  rw [entry.returnedCompletion?_resumeWithFuel_stable
    (TrapReason := TrapReason) additional completion completed]

end Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution
