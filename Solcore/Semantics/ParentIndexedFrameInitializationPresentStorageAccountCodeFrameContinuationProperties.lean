import Solcore.Semantics.ParentIndexedFrameInitializationPresentStorageAccountCodeFrameContinuation
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeFrameContinuationProperties
import Solcore.Semantics.ParentIndexedFrameInitializationPresentStorageAccountProperties

/-! Exact result-shape laws for parent-indexed selected frame construction. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameInitialization

universe u v w

/-- The outer boundary fails exactly when the selected storage Account is absent. -/
@[simp] theorem
    runCodeWithStorageParentIndexedContinuationContext?_eq_none_iff
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress codeAddress : Address)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress codeAddress fuel doneOutcome = none ↔
      initialization.initialWorld.account? storageAddress = none := by
  cases observed : initialization.initialWorld.account? storageAddress with
  | none =>
      unfold runCodeWithStorageParentIndexedContinuationContext?
      rw [toCheckpointedWorkingPairWithPresentStorageAccount?_of_absent
        initialization storageAddress observed]
      simp only [Option.map_none]
  | some account =>
      unfold runCodeWithStorageParentIndexedContinuationContext?
      rw [toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
        initialization storageAddress account observed]
      simp only [Option.map_some, Option.some_ne_none]

/-- The second boundary fails exactly when selected code is absent. -/
theorem runCodeWithStorageParentIndexedContinuationContext?_eq_some_none_iff
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress codeAddress : Address)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress codeAddress fuel doneOutcome = some none ↔
      ∃ context,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.context.values.working.1.code? codeAddress = none := by
  unfold runCodeWithStorageParentIndexedContinuationContext?
  constructor
  · intro observed
    rw [Option.map_eq_some_iff] at observed
    obtain ⟨context, refined, selected⟩ := observed
    have lowerNone := Option.map_eq_none_iff.mp selected
    exact ⟨context, refined,
      (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_none_iff
        context codeAddress fuel doneOutcome).mp lowerNone⟩
  · rintro ⟨context, refined, codeAbsent⟩
    have selected :=
      (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_none_iff
        context codeAddress fuel doneOutcome).mpr codeAbsent
    rw [refined]
    simp only [Option.map_some]
    rw [selected]
    rfl

/-- The third boundary fails exactly when selected execution exhausts fuel. -/
theorem
    runCodeWithStorageParentIndexedContinuationContext?_eq_some_some_none_iff
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress codeAddress : Address)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress codeAddress fuel doneOutcome = some (some none) ↔
      ∃ context resultContext exhausted,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.runCodeWithStorage? codeAddress fuel =
          some ⟨resultContext, .outOfFuel exhausted⟩ := by
  unfold runCodeWithStorageParentIndexedContinuationContext?
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
      (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_some_none_iff
        context codeAddress fuel doneOutcome).mp ran
    exact ⟨context, resultContext, exhausted, refined, exactRun⟩
  · rintro ⟨context, resultContext, exhausted, refined, exactRun⟩
    have selected :=
      (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_some_none_iff
        context codeAddress fuel doneOutcome).mpr
          ⟨resultContext, exhausted, exactRun⟩
    rw [refined]
    simp only [Option.map_some]
    rw [selected]
    rfl

/--
The completed branch is exactly the existing plain continuation followed by
the canonical parent-indexed reconstruction.
-/
theorem
    runCodeWithStorageParentIndexedContinuationContext?_eq_some_some_some_iff
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress codeAddress : Address)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress codeAddress fuel doneOutcome =
        some (some (some parentContinuation)) ↔
      ∃ context continuation,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.runCodeWithStorageContinuationContext?
            codeAddress fuel doneOutcome = some (some continuation) ∧
        parentContinuation =
          ParentIndexedFrameContinuationContext.fromTraceExtension
            parentWorking initialization.workingRollback
            initialization.initialTraceExtension continuation.result := by
  unfold runCodeWithStorageParentIndexedContinuationContext?
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
