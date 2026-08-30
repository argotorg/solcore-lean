import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionPreservationProperties
import Solcore.Semantics.ParentIndexedFrameInitializationProperties
import Solcore.Semantics.ParentIndexedFrameInitializationSelectedExecutionProperties
import Solcore.Semantics.ParentIndexedSelectedExecutionCompatibilityProperties

/-! Completed continuation coherence for branch-complete selected execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameInitialization

universe u v w

open ParentIndexedSelectedExecutionResult

/--
The canonical completed parent context forgets to the exact plain context from
the final driver values. This uses actual refinement and execution evidence.
-/
theorem completedContinuation_toFrameContinuationContext
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (initialContext finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some initialContext)
    (fuel : Nat)
    (value : Core.Value)
    (store : Core.Store)
    (execution :
      initialContext.runCodeWithStorage? inputs fuel =
        some ⟨finalContext, .done value store⟩)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    (completedContinuation initialization doneOutcome
      finalContext value store).toFrameContinuationContext =
      FrameContinuationContext.fromCheckpointedWorkingPair
        finalContext.context.values
        (doneOutcome finalContext value store) := by
  have initialValues :
      initialContext.context.values = initialization.toCheckpointedWorkingPair := by
    unfold toCheckpointedWorkingPairWithPresentStorageAccount? at refined
    unfold FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?
      at refined
    split at refined
    · contradiction
    · have exactContext := Option.some.inj refined
      subst initialContext
      rfl
  have checkpointPreserved :=
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_checkpoint
      initialContext inputs fuel
      (HostDriverResult.mk finalContext (.done value store)) execution
  have effectsPreserved :=
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_workingEffects
      initialContext inputs fuel
      (HostDriverResult.mk finalContext (.done value store)) execution
  have finalCheckpoint :
      finalContext.context.values.checkpoint =
        FrameCheckpointSnapshot.fromWorkingPair parentWorking := by
    rw [checkpointPreserved, initialValues, toCheckpointedWorkingPair_eq]
  have finalEffects :
      finalContext.context.values.working.2 =
        ⟨initialization.workingRollback, parentWorking.2.trace⟩ := by
    rw [effectsPreserved, initialValues, toCheckpointedWorkingPair_eq]
  unfold completedContinuation
  unfold ParentIndexedFrameContinuationContext.fromTraceExtension
  unfold FrameContinuationContext.fromCheckpointedWorkingPair
  simp only [initialTraceExtension_toTrace]
  rw [finalCheckpoint, finalEffects]
  rfl

/-- An actual completed producer exposes its exact final plain context. -/
theorem runCodeWithStorageParentIndexedResult_completed_toFrameContinuationContext
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome =
        .completed finalContext value store continuation) :
    continuation.toFrameContinuationContext =
      FrameContinuationContext.fromCheckpointedWorkingPair
        finalContext.context.values
        (doneOutcome finalContext value store) := by
  obtain ⟨initialContext, refined, execution, continuationEq⟩ :=
    (runCodeWithStorageParentIndexedResult_eq_completed_iff
      initialization storageAddress inputs fuel doneOutcome finalContext
      value store continuation).mp completed
  subst continuation
  exact completedContinuation_toFrameContinuationContext
    initialization storageAddress inputs initialContext finalContext refined
    fuel value store execution doneOutcome

/-- The legacy API exposes the same proof-bearing completed continuation. -/
theorem runCodeWithStorageParentIndexedResult_completed_toLegacy
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome =
        .completed finalContext value store continuation) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs fuel doneOutcome =
      some (some (some continuation)) := by
  calc
    _ = (initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome).toLegacy :=
        (runCodeWithStorageParentIndexedResult_toLegacy
          initialization storageAddress inputs fuel doneOutcome).symm
    _ = some (some (some continuation)) := by rw [completed]; rfl

end Solcore.Semantics.ParentIndexedFrameInitialization
