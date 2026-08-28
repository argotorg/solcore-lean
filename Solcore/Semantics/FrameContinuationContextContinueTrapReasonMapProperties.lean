import Solcore.Semantics.FrameRunContinuationProperties
import Solcore.Semantics.FrameContinuationContextProperties
import Solcore.Semantics.FrameContinuationContextTrapReasonMapProperties

/-! Invariance of continuation results under trap-reason mapping. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameContinuationContext

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

end Solcore.Semantics.FrameContinuationContext
