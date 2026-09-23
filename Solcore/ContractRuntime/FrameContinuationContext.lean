import Solcore.ContractRuntime.FrameRun

/-! Nominal bundle for one completed frame's continuation inputs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v w x

/-- Caller-owned inputs needed to continue after one completed frame. -/
structure FrameContinuationContext
    (RollbackState : Type u) (TraceState : Type v)
    (TrapReason : Type w) : Type (max u v w) where
  stateCheckpoint : WorldState
  effectCheckpoint : FrameEffectJournal RollbackState TraceState
  effectWorking : FrameEffectJournal RollbackState TraceState
  result : FrameRunResult TrapReason

namespace FrameContinuationContext

/-- Continue through the bundled inputs using synchronized frame resolution. -/
def continue?
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    Option Next :=
  context.result.continueWithResolvedStateAndEffects?
    context.stateCheckpoint context.effectCheckpoint context.effectWorking next

end FrameContinuationContext

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextProperties`
-/

/-! Coherence of the nominal frame continuation bundle. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContext

universe u v w x

theorem continue?_eq_continueWithResolvedStateAndEffects?
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    context.continue? next =
      context.result.continueWithResolvedStateAndEffects?
        context.stateCheckpoint context.effectCheckpoint context.effectWorking
        next := by
  rfl

end Solcore.ContractRuntime.FrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextTrapReasonMap`
-/

/-! Checkpoint-preserving mapping of continuation-context trap reasons. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContext

universe u v w x

/-- Preserve caller-owned inputs while mapping only the completed result. -/
def mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContext RollbackState TraceState TrapReason) :
    FrameContinuationContext RollbackState TraceState MappedTrapReason :=
  {
    stateCheckpoint := context.stateCheckpoint
    effectCheckpoint := context.effectCheckpoint
    effectWorking := context.effectWorking
    result := context.result.mapTrapReason mapReason
  }

end Solcore.ContractRuntime.FrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextTrapReasonMapProperties`
-/

/-! Construction, projection, and composition laws for context mapping. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContext

universe u v w x y

@[simp] theorem mapTrapReason_mk
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason) :
    mapTrapReason mapReason
        (⟨stateCheckpoint, effectCheckpoint, effectWorking, result⟩ :
          FrameContinuationContext RollbackState TraceState TrapReason) =
      (⟨stateCheckpoint, effectCheckpoint, effectWorking,
        result.mapTrapReason mapReason⟩ :
          FrameContinuationContext RollbackState TraceState MappedTrapReason) := by
  rfl

@[simp] theorem stateCheckpoint_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    (mapTrapReason mapReason context).stateCheckpoint =
      context.stateCheckpoint := by
  rfl

@[simp] theorem effectCheckpoint_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    (mapTrapReason mapReason context).effectCheckpoint =
      context.effectCheckpoint := by
  rfl

@[simp] theorem effectWorking_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    (mapTrapReason mapReason context).effectWorking =
      context.effectWorking := by
  rfl

@[simp] theorem result_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    (mapTrapReason mapReason context).result =
      context.result.mapTrapReason mapReason := by
  rfl

@[simp] theorem mapTrapReason_id
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    mapTrapReason (fun reason => reason) context = context := by
  cases context with
  | mk stateCheckpoint effectCheckpoint effectWorking result =>
      rw [mapTrapReason_mk, FrameRunResult.mapTrapReason_id]

@[simp] theorem mapTrapReason_comp
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {IntermediateTrapReason : Type y}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    mapTrapReason second (mapTrapReason first context) =
      mapTrapReason (fun reason => second (first reason)) context := by
  cases context with
  | mk stateCheckpoint effectCheckpoint effectWorking result =>
      rw [mapTrapReason_mk, mapTrapReason_mk, mapTrapReason_mk,
        FrameRunResult.mapTrapReason_comp]

end Solcore.ContractRuntime.FrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextContinueTrapReasonMapProperties`
-/

/-! Invariance of continuation results under trap-reason mapping. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContext

universe u v w x y

@[simp] theorem continue?_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x} {Next : Type y}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Option Next) :
    (mapTrapReason mapReason context).continue? next =
      context.continue? next := by
  cases context with
  | mk stateCheckpoint effectCheckpoint effectWorking result =>
      cases result with
      | mk working outcome =>
          cases outcome <;>
            simp [continue?_eq_continueWithResolvedStateAndEffects?]

end Solcore.ContractRuntime.FrameContinuationContext
