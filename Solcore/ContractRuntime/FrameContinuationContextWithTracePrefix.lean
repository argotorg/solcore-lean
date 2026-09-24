import Solcore.ContractRuntime.FrameResolutionResult
import Solcore.ContractRuntime.FrameTrace
import Solcore.ContractRuntime.FrameContinuationContext

/-! A frame continuation context carrying an ordered trace-prefix invariant. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v w

/-- A continuation context whose checkpoint trace prefixes its working trace. -/
structure FrameContinuationContextWithTracePrefix
    (RollbackState : Type u) (Event : Type v)
    (TrapReason : Type w)
    extends FrameContinuationContext
      RollbackState (FrameTrace Event) TrapReason where
  tracePrefix :
    FrameTrace.IsPrefixOf effectCheckpoint.trace effectWorking.trace

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextWithTracePrefixTrapReasonMap`
-/

/-! Trap-reason mapping for continuation contexts with trace-prefix evidence. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContextWithTracePrefix

universe u v w x

/-- Map only the base context's trap reason, retaining exact prefix evidence. -/
def mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContextWithTracePrefix RollbackState Event TrapReason) :
    FrameContinuationContextWithTracePrefix
      RollbackState Event MappedTrapReason :=
  {
    toFrameContinuationContext :=
      context.toFrameContinuationContext.mapTrapReason mapReason
    tracePrefix := context.tracePrefix
  }

end Solcore.ContractRuntime.FrameContinuationContextWithTracePrefix

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextWithTracePrefixTrapReasonMapProperties`
-/

/-! Construction, projection, and composition laws for refined context mapping. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContextWithTracePrefix

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
  | mk context tracePrefix =>
      cases context with
      | mk stateCheckpoint effectCheckpoint effectWorking result =>
          cases result with
          | mk working outcome =>
              cases outcome <;> rfl

end Solcore.ContractRuntime.FrameContinuationContextWithTracePrefix
