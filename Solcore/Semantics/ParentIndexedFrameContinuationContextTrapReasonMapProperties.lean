import Solcore.Semantics.ParentIndexedFrameContinuationContextTrapReasonMap
import Solcore.Semantics.FrameContinuationContextWithTracePrefixTrapReasonMapProperties

/-! Construction, projection, and composition laws for indexed context mapping. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w x y

@[simp] theorem mapTrapReason_mk
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContextWithTracePrefix
      RollbackState Event TrapReason)
    (checkpointEq :
      (context.stateCheckpoint, context.effectCheckpoint) = parentWorking) :
    mapTrapReason mapReason
        (⟨context, checkpointEq⟩ : ParentIndexedFrameContinuationContext
          RollbackState Event TrapReason parentWorking) =
      (⟨context.mapTrapReason mapReason, checkpointEq⟩ :
        ParentIndexedFrameContinuationContext
          RollbackState Event MappedTrapReason parentWorking) := by
  rfl

@[simp] theorem toFrameContinuationContextWithTracePrefix_mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (mapTrapReason mapReason context).toFrameContinuationContextWithTracePrefix =
      context.toFrameContinuationContextWithTracePrefix.mapTrapReason mapReason := by
  rfl

@[simp] theorem mapTrapReason_id
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    mapTrapReason (fun reason => reason) context = context := by
  cases context with
  | mk context checkpointEq => simp

@[simp] theorem mapTrapReason_comp
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {IntermediateTrapReason : Type y}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    mapTrapReason second (mapTrapReason first context) =
      mapTrapReason (fun reason => second (first reason)) context := by
  cases context with
  | mk context checkpointEq => simp

end Solcore.Semantics.ParentIndexedFrameContinuationContext
