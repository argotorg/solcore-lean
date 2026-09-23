import Solcore.ContractRuntime.FrameCheckpointedWorkingPair
import Solcore.ContractRuntime.FrameTrace
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeFrameContinuation
import Solcore.ContractRuntime.ParentIndexedFrameContinuationConstruction
import Solcore.ContractRuntime.FrameContinuationContextFromCheckpointedWorkingPair

/-! Parent-indexed construction of initial frame state values. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

/-- Caller-supplied initial state values relative to one parent working pair. -/
structure ParentIndexedFrameInitialization
    (RollbackState : Type u) (Event : Type v)
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) :
    Type (max u v) where
  initialWorld : WorldState
  workingRollback : RollbackState

namespace ParentIndexedFrameInitialization

/-- Start an event-only trace extension at the indexed parent trace. -/
def initialTraceExtension
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (_initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    FrameTrace.ExtensionFrom parentWorking.2.trace :=
  FrameTrace.ExtensionFrom.start parentWorking.2.trace

/-- Build checkpointed values from the parent and caller-supplied state. -/
def toCheckpointedWorkingPair
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    FrameCheckpointedWorkingPair RollbackState (FrameTrace Event) :=
  ⟨FrameCheckpointSnapshot.fromWorkingPair parentWorking,
    (initialization.initialWorld,
      ⟨initialization.workingRollback,
        initialization.initialTraceExtension.toTrace⟩)⟩

end ParentIndexedFrameInitialization

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationProperties`
-/

/-! Canonical observation laws for parent-indexed frame initialization. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v

/-- The initial extension observes the exact indexed parent trace. -/
@[simp] theorem initialTraceExtension_toTrace
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    initialization.initialTraceExtension.toTrace =
      parentWorking.2.trace := by
  exact FrameTrace.ExtensionFrom.toTrace_start parentWorking.2.trace

/-- The derived carrier has the parent checkpoint and supplied initial state. -/
@[simp] theorem toCheckpointedWorkingPair_eq
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    initialization.toCheckpointedWorkingPair =
      ⟨FrameCheckpointSnapshot.fromWorkingPair parentWorking,
        (initialization.initialWorld,
          ⟨initialization.workingRollback, parentWorking.2.trace⟩)⟩ := by
  simp [toCheckpointedWorkingPair]

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationStorageAddress`
-/

/-! Canonical storage-address wiring for parent-indexed initialization. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v

/-- Bind one storage selector to the initialized checkpointed working values. -/
def toCheckpointedWorkingPairWithStorageAddress
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    FrameCheckpointedWorkingPairWithStorageAddress
      RollbackState (FrameTrace Event) :=
  ⟨storageAddress, initialization.toCheckpointedWorkingPair⟩

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationStorageAddressProperties`
-/

/-! Projection laws for storage-address initialization wiring. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v

@[simp] theorem
    storageAddress_toCheckpointedWorkingPairWithStorageAddress
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    (initialization.toCheckpointedWorkingPairWithStorageAddress
      storageAddress).storageAddress = storageAddress := by
  rfl

@[simp] theorem values_toCheckpointedWorkingPairWithStorageAddress
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    (initialization.toCheckpointedWorkingPairWithStorageAddress
      storageAddress).values = initialization.toCheckpointedWorkingPair := by
  rfl

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccount`
-/

/-! Present-storage refinement for parent-indexed initialization. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v

/-- Refine the initialized storage selector exactly when its Account exists. -/
def toCheckpointedWorkingPairWithPresentStorageAccount?
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    Option
      (FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState (FrameTrace Event)) :=
  (initialization.toCheckpointedWorkingPairWithStorageAddress
    storageAddress).withPresentStorageAccount?

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccountProperties`
-/

/-! Branch laws for parent-indexed initialization storage refinement. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v

/-- An absent Account keeps the initialization refinement unavailable. -/
@[simp] theorem
    toCheckpointedWorkingPairWithPresentStorageAccount?_of_absent
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (absent :
      initialization.initialWorld.account? storageAddress = none) :
    initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress = none := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?_of_absent
      (initialization.toCheckpointedWorkingPairWithStorageAddress storageAddress)
      absent

/-- A present Account returns its exact initialized evidence carrier. -/
@[simp] theorem
    toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (account : Account)
    (present :
      initialization.initialWorld.account? storageAddress = some account) :
    initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress =
      some
        ⟨initialization.toCheckpointedWorkingPairWithStorageAddress
            storageAddress,
          account,
          present⟩ := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?_of_present
      (initialization.toCheckpointedWorkingPairWithStorageAddress storageAddress)
      account present

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccountCodeFrameContinuation`
-/

/-! Parent-indexed continuation construction with immutable execution input. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

/-- Lift the same input through storage selection, execution, and completion. -/
def runCodeWithStorageParentIndexedContinuationContext?
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
    Option
      (Option
        (Option
          (ParentIndexedFrameContinuationContext
            RollbackState Event TrapReason parentWorking))) :=
  (initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress).map fun context =>
    (context.runCodeWithStorageContinuationContext?
      inputs fuel doneOutcome).map fun completed =>
        completed.map fun continuation =>
          ParentIndexedFrameContinuationContext.fromTraceExtension
            parentWorking initialization.workingRollback
            initialization.initialTraceExtension continuation.result

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccountCodeFrameContinuationProperties`
-/

/-! Result-shape laws for parent-indexed execution with immutable input. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

@[simp] theorem
    runCodeWithStorageParentIndexedContinuationContext?_eq_none_iff
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
    initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome = none ↔
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

theorem
    runCodeWithStorageParentIndexedContinuationContext?_eq_some_none_iff
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
    initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome = some none ↔
      ∃ context,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.context.values.working.1.code? inputs.codeAddress = none := by
  unfold runCodeWithStorageParentIndexedContinuationContext?
  constructor
  · intro observed
    rw [Option.map_eq_some_iff] at observed
    obtain ⟨context, refined, selected⟩ := observed
    have lowerNone := Option.map_eq_none_iff.mp selected
    exact ⟨context, refined,
      (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_none_iff
        context inputs fuel doneOutcome).mp lowerNone⟩
  · rintro ⟨context, refined, codeAbsent⟩
    have selected :=
      (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_none_iff
        context inputs fuel doneOutcome).mpr codeAbsent
    rw [refined]
    simp only [Option.map_some]
    rw [selected]
    rfl

theorem
    runCodeWithStorageParentIndexedContinuationContext?_eq_some_some_none_iff
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
    initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome = some (some none) ↔
      (∃ context resultContext exhausted,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.runCodeWithStorage? inputs fuel =
          some ⟨resultContext, .outOfFuel exhausted⟩) ∨
      ∃ context resultContext suspension remainingFuel,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.runCodeWithStorage? inputs fuel =
          some ⟨resultContext,
            .unsupported suspension remainingFuel⟩ := by
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
    rcases
      (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_some_none_iff
        context inputs fuel doneOutcome).mp ran with
      ⟨⟨resultContext, exhausted, exactRun⟩⟩ |
        ⟨resultContext, suspension, remainingFuel, exactRun⟩
    · exact .inl ⟨context, resultContext, exhausted, refined, exactRun⟩
    · exact .inr
        ⟨context, resultContext, suspension, remainingFuel, refined, exactRun⟩
  · intro observed
    rcases observed with
      ⟨context, resultContext, exhausted, refined, exactRun⟩ |
      ⟨context, resultContext, suspension, remainingFuel, refined, exactRun⟩
    · have selected :=
        (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_some_none_iff
          context inputs fuel doneOutcome).mpr
            (.inl ⟨resultContext, exhausted, exactRun⟩)
      rw [refined]
      simp only [Option.map_some]
      rw [selected]
      rfl
    · have selected :=
        (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_some_none_iff
          context inputs fuel doneOutcome).mpr
            (.inr ⟨resultContext, suspension, remainingFuel, exactRun⟩)
      rw [refined]
      simp only [Option.map_some]
      rw [selected]
      rfl

theorem
    runCodeWithStorageParentIndexedContinuationContext?_eq_some_some_some_iff
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
    initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation)) ↔
      ∃ context continuation,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.runCodeWithStorageContinuationContext?
            inputs fuel doneOutcome = some (some continuation) ∧
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

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccountCodeFrameContinuationCoherenceProperties`
-/

/-! Coherence and stability for parent-indexed explicit-input execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

private theorem completedContinuation_eq_parentIndexed
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
      | unsupported suspension remainingFuel => simp at resultCompleted
      | outOfFuel exhausted => simp at resultCompleted
      | fault error faultState => simp at resultCompleted

theorem
    runCodeWithStorageParentIndexedContinuationContext?_some_some_some_toFrameContinuationContext
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
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation))) :
    ∃ context continuation,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context ∧
      context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = some (some continuation) ∧
      parentContinuation.toFrameContinuationContext = continuation := by
  unfold runCodeWithStorageParentIndexedContinuationContext?
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
    completedContinuation_eq_parentIndexed initialization
      storageAddress inputs context refined fuel doneOutcome continuation
      lowerCompleted⟩

theorem
    runCodeWithStorageParentIndexedContinuationContext?_some_some_some_stable
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
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation)))
    (more : fuel ≤ largerFuel) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs largerFuel doneOutcome =
      some (some (some parentContinuation)) := by
  rw [
    runCodeWithStorageParentIndexedContinuationContext?_eq_some_some_some_iff]
    at completed ⊢
  obtain ⟨context, continuation, refined, lowerCompleted, parentEq⟩ :=
    completed
  exact ⟨context, continuation, refined,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_some_some_stable
      context inputs doneOutcome lowerCompleted more,
    parentEq⟩

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationContinuationContextCoherenceProperties`
-/

/-! Coherence of two continuation-context routes from indexed initialization. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

/-- Both pure initialization routes produce the same plain continuation context. -/
theorem toFrameContinuationContext_fromTraceExtension_eq_fromCheckpointedWorkingPair
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (outcome : FrameOutcome TrapReason) :
    (ParentIndexedFrameContinuationContext.fromTraceExtension
      parentWorking initialization.workingRollback
      initialization.initialTraceExtension
      ⟨initialization.initialWorld, outcome⟩).toFrameContinuationContext =
      FrameContinuationContext.fromCheckpointedWorkingPair
        initialization.toCheckpointedWorkingPair outcome := by
  rfl

end Solcore.ContractRuntime.ParentIndexedFrameInitialization
