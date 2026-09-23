import Solcore.ContractRuntime.FrameResolutionResult

/-! Compile-only regressions for result-continuation reason-map invariance. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

universe u v w x y z

private example
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {Next : Type y}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameResolutionResult RollbackState TraceState TrapReason)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    (result.mapTrapReason mapReason).continue?
        onReturned onReverted =
      result.continue? onReturned onReverted := by
  simp

private example
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {IntermediateTrapReason : Type x}
    {MappedTrapReason : Type y} {Next : Type z}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (result : FrameResolutionResult RollbackState TraceState TrapReason)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    ((result.mapTrapReason first).mapTrapReason second).continue?
        onReturned onReverted =
      result.continue? onReturned onReverted := by
  simp

end Tests
