import Solcore.Semantics.FrameContinuationContextTrapReasonMap
import Solcore.Semantics.FrameRunResultTrapReasonMapProperties

/-! Construction, projection, and composition laws for context mapping. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameContinuationContext

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

end Solcore.Semantics.FrameContinuationContext
