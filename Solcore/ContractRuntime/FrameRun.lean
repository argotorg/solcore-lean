import Solcore.ContractRuntime.FrameStateResolution
import Solcore.ContractRuntime.FrameOutcome
import Solcore.ContractRuntime.FrameEffectJournal

/-! Frame-run results, continuation, effect resolution, and their laws. -/

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunResult`
-/

/-! The minimal state-and-outcome payload produced by one frame run. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u

/-- A speculative working state paired with the frame outcome it produced. -/
structure FrameRunResult (TrapReason : Type u) : Type u where
  working : WorldState
  outcome : FrameOutcome TrapReason

namespace FrameRunResult

/-- Resolve a frame result against a checkpoint still owned by the caller. -/
def resolvedWorldState?
    {TrapReason : Type u}
    (checkpoint : WorldState)
    (result : FrameRunResult TrapReason) : Option WorldState :=
  FrameOutcome.resolvedWorldState?
    checkpoint result.working result.outcome

end FrameRunResult

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunResultProperties`
-/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u

@[simp] theorem resolvedWorldState?_returned
    {TrapReason : Type u}
    (checkpoint working : WorldState) (data : Bytes) :
    FrameRunResult.resolvedWorldState? checkpoint
        (⟨working, .returned data⟩ : FrameRunResult TrapReason) =
      some working := by
  rfl

@[simp] theorem resolvedWorldState?_reverted
    {TrapReason : Type u}
    (checkpoint working : WorldState) (data : Bytes) :
    FrameRunResult.resolvedWorldState? checkpoint
        (⟨working, .reverted data⟩ : FrameRunResult TrapReason) =
      some checkpoint := by
  rfl

@[simp] theorem resolvedWorldState?_trapped
    {TrapReason : Type u}
    (checkpoint working : WorldState) (reason : TrapReason) :
    FrameRunResult.resolvedWorldState? checkpoint
        (⟨working, .trapped reason⟩ : FrameRunResult TrapReason) = none := by
  rfl

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunResultTrapReasonMap`
-/

/-! Working-state-preserving mapping of frame-run trap-reason types. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v

/-- Preserve the working state while mapping only the result's trapped reason. -/
def mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    FrameRunResult MappedTrapReason :=
  ⟨result.working, result.outcome.mapTrapReason mapReason⟩

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunResultTrapReasonMapProperties`
-/

/-! Construction, projection, and composition laws for frame-result mapping. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w

@[simp] theorem mapTrapReason_mk
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (working : WorldState) (outcome : FrameOutcome TrapReason) :
    mapTrapReason mapReason ⟨working, outcome⟩ =
      (⟨working, outcome.mapTrapReason mapReason⟩ :
        FrameRunResult MappedTrapReason) := by
  rfl

@[simp] theorem working_mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    (mapTrapReason mapReason result).working = result.working := by
  rfl

@[simp] theorem outcome_mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    (mapTrapReason mapReason result).outcome =
      result.outcome.mapTrapReason mapReason := by
  rfl

@[simp] theorem mapTrapReason_id
    {TrapReason : Type u} (result : FrameRunResult TrapReason) :
    mapTrapReason (fun reason => reason) result = result := by
  cases result with
  | mk working outcome =>
      rw [mapTrapReason_mk, FrameOutcome.mapTrapReason_id]

@[simp] theorem mapTrapReason_comp
    {TrapReason : Type u}
    {IntermediateTrapReason : Type v}
    {MappedTrapReason : Type w}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    mapTrapReason second (mapTrapReason first result) =
      mapTrapReason (fun reason => second (first reason)) result := by
  cases result with
  | mk working outcome =>
      rw [mapTrapReason_mk, mapTrapReason_mk, mapTrapReason_mk,
        FrameOutcome.mapTrapReason_comp]

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunEffectResolution`
-/

/-! Synchronized resolution of one frame's WorldState and effect journal. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w

/-- Resolve state and effects from the same outcome without choosing trap policy. -/
def resolvedWorldStateAndEffects?
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason) :
    Option (WorldState × FrameEffectJournal RollbackState TraceState) :=
  match result.outcome with
  | .returned _ => some (result.working, effectWorking)
  | .reverted _ =>
      some (stateCheckpoint,
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩)
  | .trapped _ => none

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunContinuation`
-/

/-! Caller-owned continuation after synchronized frame resolution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w x

/-- Resolve caller-supplied state and effects before invoking a continuation. -/
def continueWithResolvedStateAndEffects?
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    Option Next :=
  (result.resolvedWorldStateAndEffects?
    stateCheckpoint effectCheckpoint effectWorking).bind next

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunContinuationProperties`
-/

/-! Constructor laws for caller-owned frame continuation. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w x

@[simp] theorem continueWithResolvedStateAndEffects?_returned
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    continueWithResolvedStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.returned
        (TrapReason := TrapReason) data⟩ : FrameRunResult TrapReason) next =
      next (workingWorld, effectWorking) := by
  rfl

@[simp] theorem continueWithResolvedStateAndEffects?_reverted
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    continueWithResolvedStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.reverted
        (TrapReason := TrapReason) data⟩ : FrameRunResult TrapReason) next =
      next (stateCheckpoint,
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩) := by
  rfl

@[simp] theorem continueWithResolvedStateAndEffects?_trapped
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    continueWithResolvedStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.trapped reason⟩ :
        FrameRunResult TrapReason) next = none := by
  rfl

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunEffectResolutionProperties`
-/

/-! Laws for synchronized frame state and effect resolution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w

@[simp] theorem resolvedWorldStateAndEffects?_returned
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.returned
        (TrapReason := TrapReason) data⟩ : FrameRunResult TrapReason) =
      some (workingWorld, effectWorking) := by
  rfl

@[simp] theorem resolvedWorldStateAndEffects?_reverted
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.reverted
        (TrapReason := TrapReason) data⟩ : FrameRunResult TrapReason) =
      some (stateCheckpoint,
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩) := by
  rfl

@[simp] theorem resolvedWorldStateAndEffects?_trapped
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason) :
    resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.trapped reason⟩ : FrameRunResult TrapReason) =
      none := by
  rfl

theorem resolvedWorldStateAndEffects?_worldState
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason) :
    Option.map Prod.fst
      (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint
        effectWorking result) =
      result.resolvedWorldState? stateCheckpoint := by
  cases result with
  | mk working outcome => cases outcome <;> rfl

theorem resolvedWorldStateAndEffects?_effects
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason) :
    Option.map Prod.snd
      (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint
        effectWorking result) =
      FrameEffectJournal.resolved? effectCheckpoint effectWorking result.outcome := by
  cases result with
  | mk working outcome => cases outcome <;> rfl

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunEffectCompositionProperties`
-/

/-! Nested composition laws for synchronized frame state and effects. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w

theorem resolvedWorldStateAndEffects?_child_return_parent_revert
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (parentStateCheckpoint childStateCheckpoint childStateWorking : WorldState)
    (parentEffectCheckpoint childEffectCheckpoint childEffectWorking :
      FrameEffectJournal RollbackState TraceState)
    (childData parentData : Bytes) :
    (resolvedWorldStateAndEffects?
      childStateCheckpoint childEffectCheckpoint childEffectWorking
      (⟨childStateWorking, FrameOutcome.returned
        (TrapReason := TrapReason) childData⟩ : FrameRunResult TrapReason)).bind
        (fun childResolved => resolvedWorldStateAndEffects?
          parentStateCheckpoint parentEffectCheckpoint childResolved.2
          (⟨childResolved.1, FrameOutcome.reverted
            (TrapReason := TrapReason) parentData⟩ : FrameRunResult TrapReason)) =
      some (parentStateCheckpoint,
        ⟨parentEffectCheckpoint.rollback, childEffectWorking.trace⟩) := by
  rfl

theorem resolvedWorldStateAndEffects?_child_revert_parent_revert
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (parentStateCheckpoint childStateCheckpoint childStateWorking : WorldState)
    (parentEffectCheckpoint childEffectCheckpoint childEffectWorking :
      FrameEffectJournal RollbackState TraceState)
    (childData parentData : Bytes) :
    (resolvedWorldStateAndEffects?
      childStateCheckpoint childEffectCheckpoint childEffectWorking
      (⟨childStateWorking, FrameOutcome.reverted
        (TrapReason := TrapReason) childData⟩ : FrameRunResult TrapReason)).bind
        (fun childResolved => resolvedWorldStateAndEffects?
          parentStateCheckpoint parentEffectCheckpoint childResolved.2
          (⟨childResolved.1, FrameOutcome.reverted
            (TrapReason := TrapReason) parentData⟩ : FrameRunResult TrapReason)) =
      some (parentStateCheckpoint,
        ⟨parentEffectCheckpoint.rollback, childEffectWorking.trace⟩) := by
  rfl

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunEffectContinuationProperties`
-/

/-! Continuation laws for resolved synchronized frame state and effects. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w x

theorem resolvedWorldStateAndEffects?_returned_bind
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.returned
        (TrapReason := TrapReason) data⟩ :
        FrameRunResult TrapReason)).bind next =
      next (workingWorld, effectWorking) := by
  rfl

theorem resolvedWorldStateAndEffects?_reverted_bind
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.reverted
        (TrapReason := TrapReason) data⟩ :
        FrameRunResult TrapReason)).bind next =
      next (stateCheckpoint,
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩) := by
  rfl

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunEffectTrapPropagationProperties`
-/

/-! Propagation of unresolved traps through synchronized frame continuations. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w x

/-- A trapped synchronized resolution cannot invoke or succeed through a continuation. -/
theorem resolvedWorldStateAndEffects?_trapped_bind
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.trapped reason⟩ :
        FrameRunResult TrapReason)).bind next = none := by
  rfl

end Solcore.ContractRuntime.FrameRunResult
