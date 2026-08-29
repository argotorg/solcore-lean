import Solcore.Semantics.ParentIndexedFrameInitializationPresentStorageAccountCodeFrameContinuationWithInputsProperties
import Solcore.Semantics.ParentIndexedFrameInitializationProperties

/-! Coherence and stability for parent-indexed explicit-input execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameInitialization

universe u v w

private theorem completedContinuationWithInputs_eq_parentIndexed
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (context :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (continuation :
      FrameContinuationContext RollbackState (FrameTrace Event) TrapReason)
    (completed :
      context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = some (some continuation)) :
    (ParentIndexedFrameContinuationContext.fromTraceExtension
      parentWorking initialization.workingRollback
      initialization.initialTraceExtension continuation.result
    ).toFrameContinuationContext = continuation := by
  have contextValues :
      context.context.values = initialization.toCheckpointedWorkingPair := by
    unfold toCheckpointedWorkingPairWithPresentStorageAccount? at refined
    unfold FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?
      at refined
    split at refined
    · contradiction
    · have exactContext := Option.some.inj refined
      subst context
      rfl
  unfold FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?
    at completed
  rw [Option.map_eq_some_iff] at completed
  obtain ⟨result, execution, resultCompleted⟩ := completed
  cases result with
  | mk finalContext outcome =>
      cases outcome with
      | done value store =>
          have continuationEq :
              FrameContinuationContext.fromCheckpointedWorkingPair
                  finalContext.context.values
                  (doneOutcome finalContext value store) = continuation := by
            simpa only [HostDriverResult.toFrameContinuationContext?_done,
              Option.some.injEq] using resultCompleted
          have checkpointPreserved :=
            FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_checkpoint
              context inputs fuel
              (HostDriverResult.mk finalContext (.done value store)) execution
          have effectsPreserved :=
            FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_workingEffects
              context inputs fuel
              (HostDriverResult.mk finalContext (.done value store)) execution
          have finalCheckpoint :
              finalContext.context.values.checkpoint =
                FrameCheckpointSnapshot.fromWorkingPair parentWorking := by
            rw [checkpointPreserved, contextValues,
              toCheckpointedWorkingPair_eq]
          have finalEffects :
              finalContext.context.values.working.2 =
                ⟨initialization.workingRollback, parentWorking.2.trace⟩ := by
            rw [effectsPreserved, contextValues,
              toCheckpointedWorkingPair_eq]
          rw [← continuationEq]
          unfold ParentIndexedFrameContinuationContext.fromTraceExtension
          unfold FrameContinuationContext.fromCheckpointedWorkingPair
          simp only [initialTraceExtension_toTrace]
          rw [finalCheckpoint, finalEffects]
          rfl
      | outOfFuel exhausted => simp at resultCompleted
      | fault error faultState => simp at resultCompleted

theorem
    runCodeWithStorageParentIndexedContinuationContextWithInputs?_some_some_some_toFrameContinuationContext
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation))) :
    ∃ context continuation,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context ∧
      context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = some (some continuation) ∧
      parentContinuation.toFrameContinuationContext = continuation := by
  unfold runCodeWithStorageParentIndexedContinuationContextWithInputs?
    at completed
  rw [Option.map_eq_some_iff] at completed
  obtain ⟨context, refined, selected⟩ := completed
  rw [Option.map_eq_some_iff] at selected
  obtain ⟨completion, ran, parentBuilt⟩ := selected
  rw [Option.map_eq_some_iff] at parentBuilt
  obtain ⟨continuation, continuationEq, parentEq⟩ := parentBuilt
  have lowerCompleted :
      context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = some (some continuation) := by
    rw [ran, continuationEq]
  subst parentContinuation
  exact ⟨context, continuation, refined, lowerCompleted,
    completedContinuationWithInputs_eq_parentIndexed initialization
      storageAddress inputs context refined fuel doneOutcome continuation
      lowerCompleted⟩

theorem
    runCodeWithStorageParentIndexedContinuationContextWithInputs?_some_some_some_stable
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    {fuel largerFuel : Nat}
    {parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking}
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation)))
    (more : fuel ≤ largerFuel) :
    initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?
        storageAddress inputs largerFuel doneOutcome =
      some (some (some parentContinuation)) := by
  rw [
    runCodeWithStorageParentIndexedContinuationContextWithInputs?_eq_some_some_some_iff]
    at completed ⊢
  obtain ⟨context, continuation, refined, lowerCompleted, parentEq⟩ :=
    completed
  exact ⟨context, continuation, refined,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_some_some_stable
      context inputs doneOutcome lowerCompleted more,
    parentEq⟩

end Solcore.Semantics.ParentIndexedFrameInitialization
