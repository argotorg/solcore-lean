import Solcore.ContractRuntime.FrameContinuationContextContinueTrapReasonMapProperties

/-! Compile-only regressions for continuation-result invariance. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

universe u v w x y z

private example
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x} {Next : Type y}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Option Next) :
    (context.mapTrapReason mapReason).continue? next = context.continue? next := by
  simp

private example
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {IntermediateTrapReason : Type x}
    {MappedTrapReason : Type y} {Next : Type z}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Option Next) :
    ((context.mapTrapReason first).mapTrapReason second).continue? next =
      context.continue? next := by
  simp

end Tests
