import Solcore.ContractRuntime.FrameContinuationContext

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
