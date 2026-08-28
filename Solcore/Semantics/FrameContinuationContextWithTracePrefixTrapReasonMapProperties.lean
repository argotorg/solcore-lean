import Solcore.Semantics.FrameContinuationContextWithTracePrefixTrapReasonMap
import Solcore.Semantics.FrameContinuationContextTrapReasonMapProperties

/-! Construction, projection, and composition laws for refined context mapping. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameContinuationContextWithTracePrefix

universe u v w x y

@[simp] theorem mapTrapReason_mk
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContext RollbackState (FrameTrace Event) TrapReason)
    (tracePrefix :
      FrameTrace.IsPrefixOf
        context.effectCheckpoint.trace context.effectWorking.trace) :
    mapTrapReason mapReason
        (⟨context, tracePrefix⟩ :
          FrameContinuationContextWithTracePrefix
            RollbackState Event TrapReason) =
      (⟨context.mapTrapReason mapReason, tracePrefix⟩ :
        FrameContinuationContextWithTracePrefix
          RollbackState Event MappedTrapReason) := by
  rfl

@[simp] theorem toFrameContinuationContext_mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContextWithTracePrefix RollbackState Event TrapReason) :
    (mapTrapReason mapReason context).toFrameContinuationContext =
      context.toFrameContinuationContext.mapTrapReason mapReason := by
  rfl

@[simp] theorem mapTrapReason_id
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    (context :
      FrameContinuationContextWithTracePrefix RollbackState Event TrapReason) :
    mapTrapReason (fun reason => reason) context = context := by
  cases context with
  | mk context tracePrefix => simp

@[simp] theorem mapTrapReason_comp
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {IntermediateTrapReason : Type y}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context :
      FrameContinuationContextWithTracePrefix RollbackState Event TrapReason) :
    mapTrapReason second (mapTrapReason first context) =
      mapTrapReason (fun reason => second (first reason)) context := by
  cases context with
  | mk context tracePrefix => simp

end Solcore.Semantics.FrameContinuationContextWithTracePrefix
