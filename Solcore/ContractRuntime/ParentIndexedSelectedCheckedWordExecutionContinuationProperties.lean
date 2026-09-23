import Solcore.ContractRuntime.ParentIndexedFrameContinuationConstructionProperties
import Solcore.ContractRuntime.ParentIndexedFrameContinuationContextProperties
import Solcore.ContractRuntime.ParentIndexedFrameInitializationProperties
import Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecutionContinuation
import Solcore.ContractRuntime.SelectedCheckedWordExecutionSafetyProperties
import Solcore.ContractRuntime.WordReturnedFrameCompletionProperties

/-! Exact branch and projection laws for canonical returned-parent completion. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

universe u v w

/-- A missing pair is exactly a missing inner Word completion. -/
theorem returnedCompletion?_eq_none_iff
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.returnedCompletion? (TrapReason := TrapReason) = none ↔
      entry.execution.completion? = none := by
  unfold returnedCompletion?
  split <;> simp_all

/-- Exact inner completion constructs the proof-linked pair. -/
theorem returnedCompletion?_of_completion
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    entry.returnedCompletion? (TrapReason := TrapReason) =
      some (completion, entry.toReturnedContinuation completion completed) := by
  unfold returnedCompletion?
  split
  · rename_i missing
    rw [completed] at missing
    contradiction
  · rename_i actual observed
    have completionEq : actual = completion :=
      Option.some.inj (observed.symm.trans completed)
    subst actual
    rfl

/-- Forgetting the parent continuation recovers the exact inner completion. -/
theorem returnedCompletion?_map_fst
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    (entry.returnedCompletion? (TrapReason := TrapReason)).map Prod.fst =
      entry.execution.completion? := by
  unfold returnedCompletion?
  split <;> simp_all

/-- The continuation-only view is definitionally derived from the pair. -/
theorem returnedContinuation?_eq_map_snd
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.returnedContinuation? (TrapReason := TrapReason) =
      (entry.returnedCompletion? (TrapReason := TrapReason)).map Prod.snd :=
  rfl

/-- Exact inner completion constructs the exact continuation-only view. -/
theorem returnedContinuation?_of_completion
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    entry.returnedContinuation? (TrapReason := TrapReason) =
      some (entry.toReturnedContinuation completion completed) := by
  rw [returnedContinuation?_eq_map_snd,
    entry.returnedCompletion?_of_completion
      (TrapReason := TrapReason) completion completed]
  rfl

/-- The parent continuation always carries canonical returned Word bytes. -/
@[simp] theorem result_toReturnedContinuation
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.toReturnedContinuation
      (TrapReason := TrapReason) completion completed).result =
      ⟨completion.context.context.values.working.1,
        .returned completion.returnData⟩ := by
  simp [toReturnedContinuation]

/-- The returned parent context resolves to final working values and bytes. -/
theorem resolve_toReturnedContinuation
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.toReturnedContinuation
        (TrapReason := TrapReason) completion completed).resolve =
      .returned completion.context.context.values.working.1
        ⟨initialization.workingRollback, parentWorking.2.trace⟩
        completion.returnData := by
  simp [toReturnedContinuation, FrameContinuationContext.resolve]

/-- The indexed parent trace prefixes every canonical returned continuation. -/
theorem parentWorking_tracePrefix_toReturnedContinuation
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    FrameTrace.IsPrefixOf parentWorking.2.trace
      (entry.toReturnedContinuation
        (TrapReason := TrapReason) completion completed).effectWorking.trace :=
  (entry.toReturnedContinuation
    (TrapReason := TrapReason) completion completed).parentWorking_tracePrefix

end Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution
