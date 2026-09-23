import Solcore.ContractRuntime.HostStorageDriverProperties
import Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecutionContinuationProperties
import Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecutionProperties

/-! Final-context and plain-continuation coherence for parent Word return. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

universe u v w

/-- The canonical parent continuation keeps the indexed parent state checkpoint. -/
@[simp] theorem stateCheckpoint_toReturnedContinuation
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
      (TrapReason := TrapReason) completion completed).stateCheckpoint =
      parentWorking.1 :=
  rfl

/-- The canonical parent continuation keeps the indexed parent effect checkpoint. -/
@[simp] theorem effectCheckpoint_toReturnedContinuation
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
      (TrapReason := TrapReason) completion completed).effectCheckpoint =
      parentWorking.2 :=
  rfl

/-- Working effects retain the initialized rollback and exact parent trace. -/
@[simp] theorem effectWorking_toReturnedContinuation
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
      (TrapReason := TrapReason) completion completed).effectWorking =
      ⟨initialization.workingRollback, parentWorking.2.trace⟩ := by
  simp [toReturnedContinuation]

/-- Successful completion preserves the exact indexed parent checkpoint. -/
theorem completion_context_checkpoint
    {RollbackState : Type u} {Event : Type v}
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
    completion.context.context.values.checkpoint =
      FrameCheckpointSnapshot.fromWorkingPair parentWorking := by
  obtain ⟨code, retained⟩ :=
    (entry.execution.completion?_eq_some_iff completion).mp completed
  have exactRun :=
    (entry.execution.execution?_eq_some_iff
      code completion.toHostDriverResult).mp retained
  have preserved :
      (code.runWithStorage entry.initialContext inputs
          entry.execution.providedFuel).context.context.values.checkpoint =
        entry.initialContext.context.values.checkpoint := by
    simpa only [CheckedHostCoreWordProgram.runWithStorage,
      CheckedHostCoreProgram.runWithStorage] using
      HostStorageDriver.run_checkpoint entry.initialContext inputs
        entry.execution.providedFuel
        (Core.State.initial code.code.program.body Core.hostEnvironment)
  rw [exactRun.2.symm] at preserved
  simpa [WordReturnedFrameCompletion.toHostDriverResult] using
    preserved.trans entry.initialContext_checkpoint

/-- Successful completion preserves the initialized rollback and parent trace. -/
theorem completion_context_workingEffects
    {RollbackState : Type u} {Event : Type v}
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
    completion.context.context.values.working.2 =
      ⟨initialization.workingRollback, parentWorking.2.trace⟩ := by
  obtain ⟨code, retained⟩ :=
    (entry.execution.completion?_eq_some_iff completion).mp completed
  have exactRun :=
    (entry.execution.execution?_eq_some_iff
      code completion.toHostDriverResult).mp retained
  have preserved :
      (code.runWithStorage entry.initialContext inputs
          entry.execution.providedFuel).context.context.values.working.2 =
        entry.initialContext.context.values.working.2 := by
    simpa only [CheckedHostCoreWordProgram.runWithStorage,
      CheckedHostCoreProgram.runWithStorage] using
      HostStorageDriver.run_workingEffects entry.initialContext inputs
        entry.execution.providedFuel
        (Core.State.initial code.code.program.body Core.hostEnvironment)
  rw [exactRun.2.symm] at preserved
  simpa [WordReturnedFrameCompletion.toHostDriverResult] using
    preserved.trans entry.initialContext_workingEffects

/-- Forgetting the parent index recovers the exact canonical plain context. -/
theorem toFrameContinuationContext_toReturnedContinuation
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
        (TrapReason := TrapReason) completion completed).toFrameContinuationContext =
      (completion.toFrameContinuationContext :
        FrameContinuationContext
          RollbackState (FrameTrace Event) TrapReason) := by
  have checkpoint := entry.completion_context_checkpoint completion completed
  have workingEffects :=
    entry.completion_context_workingEffects completion completed
  unfold toReturnedContinuation
  unfold ParentIndexedFrameContinuationContext.fromTraceExtension
  unfold WordReturnedFrameCompletion.toFrameContinuationContext
  unfold FrameContinuationContext.fromCheckpointedWorkingPair
  simp only [initialization.initialTraceExtension_toTrace]
  rw [checkpoint, workingEffects]
  rfl

/-- Exact pair output is equivalent to exact completion plus its constructor. -/
theorem returnedCompletion?_eq_some_iff
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
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    entry.returnedCompletion? (TrapReason := TrapReason) =
        some (completion, continuation) ↔
      ∃ completed : entry.execution.completion? = some completion,
        continuation = entry.toReturnedContinuation completion completed := by
  constructor
  · intro returned
    have completed : entry.execution.completion? = some completion := by
      have first := congrArg (Option.map Prod.fst) returned
      simpa [entry.returnedCompletion?_map_fst
        (TrapReason := TrapReason)] using first
    refine ⟨completed, ?_⟩
    rw [entry.returnedCompletion?_of_completion
      (TrapReason := TrapReason) completion completed] at returned
    exact congrArg Prod.snd (Option.some.inj returned).symm
  · rintro ⟨completed, rfl⟩
    exact entry.returnedCompletion?_of_completion
      (TrapReason := TrapReason) completion completed

end Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution
