import Solcore.Semantics.FrameContinuationContextResolveTrapReasonMapProperties

/-! Compile-only regressions for resolution naturality. -/

set_option autoImplicit false

namespace Tests

open Solcore.Semantics

universe u v w x y

private example
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    (context.mapTrapReason mapReason).resolve =
      context.resolve.mapTrapReason mapReason := by
  simp

private example
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {IntermediateTrapReason : Type x}
    {MappedTrapReason : Type y}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    ((context.mapTrapReason first).mapTrapReason second).resolve =
      context.resolve.mapTrapReason
        (fun reason => second (first reason)) := by
  simp

end Tests
