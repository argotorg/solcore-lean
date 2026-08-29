import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeFrameContinuationWithInputsProperties
import Solcore.Semantics.ParentIndexedFrameInitializationPresentStorageAccountCodeFrameContinuationWithInputs
import Solcore.Semantics.ParentIndexedFrameInitializationPresentStorageAccountProperties

/-! Result-shape laws for parent-indexed execution with immutable input. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameInitialization

universe u v w

@[simp] theorem
    runCodeWithStorageParentIndexedContinuationContextWithInputs?_eq_none_iff
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
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?
          storageAddress inputs fuel doneOutcome = none ↔
      initialization.initialWorld.account? storageAddress = none := by
  cases observed : initialization.initialWorld.account? storageAddress with
  | none =>
      unfold runCodeWithStorageParentIndexedContinuationContextWithInputs?
      rw [toCheckpointedWorkingPairWithPresentStorageAccount?_of_absent
        initialization storageAddress observed]
      simp only [Option.map_none]
  | some account =>
      unfold runCodeWithStorageParentIndexedContinuationContextWithInputs?
      rw [toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
        initialization storageAddress account observed]
      simp only [Option.map_some, Option.some_ne_none]

theorem
    runCodeWithStorageParentIndexedContinuationContextWithInputs?_eq_some_none_iff
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
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?
          storageAddress inputs fuel doneOutcome = some none ↔
      ∃ context,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.context.values.working.1.code? inputs.codeAddress = none := by
  unfold runCodeWithStorageParentIndexedContinuationContextWithInputs?
  constructor
  · intro observed
    rw [Option.map_eq_some_iff] at observed
    obtain ⟨context, refined, selected⟩ := observed
    have lowerNone := Option.map_eq_none_iff.mp selected
    exact ⟨context, refined,
      (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContextWithInputs?_eq_none_iff
        context inputs fuel doneOutcome).mp lowerNone⟩
  · rintro ⟨context, refined, codeAbsent⟩
    have selected :=
      (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContextWithInputs?_eq_none_iff
        context inputs fuel doneOutcome).mpr codeAbsent
    rw [refined]
    simp only [Option.map_some]
    rw [selected]
    rfl

theorem
    runCodeWithStorageParentIndexedContinuationContextWithInputs?_eq_some_some_none_iff
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
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?
          storageAddress inputs fuel doneOutcome = some (some none) ↔
      ∃ context resultContext exhausted,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.runCodeWithStorage? inputs fuel =
          some ⟨resultContext, .outOfFuel exhausted⟩ := by
  unfold runCodeWithStorageParentIndexedContinuationContextWithInputs?
  constructor
  · intro observed
    rw [Option.map_eq_some_iff] at observed
    obtain ⟨context, refined, selected⟩ := observed
    rw [Option.map_eq_some_iff] at selected
    obtain ⟨completion, ran, built⟩ := selected
    have completionEq : completion = none := by
      simpa only [Option.map_eq_none_iff] using built
    subst completion
    obtain ⟨resultContext, exhausted, exactRun⟩ :=
      (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContextWithInputs?_eq_some_none_iff
        context inputs fuel doneOutcome).mp ran
    exact ⟨context, resultContext, exhausted, refined, exactRun⟩
  · rintro ⟨context, resultContext, exhausted, refined, exactRun⟩
    have selected :=
      (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContextWithInputs?_eq_some_none_iff
        context inputs fuel doneOutcome).mpr
          ⟨resultContext, exhausted, exactRun⟩
    rw [refined]
    simp only [Option.map_some]
    rw [selected]
    rfl

theorem
    runCodeWithStorageParentIndexedContinuationContextWithInputs?_eq_some_some_some_iff
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
        RollbackState Event TrapReason parentWorking) :
    initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation)) ↔
      ∃ context continuation,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.runCodeWithStorageContinuationContextWithInputs?
            inputs fuel doneOutcome = some (some continuation) ∧
        parentContinuation =
          ParentIndexedFrameContinuationContext.fromTraceExtension
            parentWorking initialization.workingRollback
            initialization.initialTraceExtension continuation.result := by
  unfold runCodeWithStorageParentIndexedContinuationContextWithInputs?
  constructor
  · intro observed
    rw [Option.map_eq_some_iff] at observed
    obtain ⟨context, refined, selected⟩ := observed
    rw [Option.map_eq_some_iff] at selected
    obtain ⟨completion, ran, built⟩ := selected
    rw [Option.map_eq_some_iff] at built
    obtain ⟨continuation, completionEq, parentEq⟩ := built
    subst completion
    exact ⟨context, continuation, refined, ran, parentEq.symm⟩
  · rintro ⟨context, continuation, refined, completed, parentEq⟩
    rw [refined]
    simp only [Option.map_some]
    rw [completed]
    simp only [Option.map_some]
    rw [← parentEq]

end Solcore.Semantics.ParentIndexedFrameInitialization
