import Solcore.Semantics.FrameRunContinuation

/-! Nominal bundle for one completed frame's continuation inputs. -/

set_option autoImplicit false

namespace Solcore.Semantics

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

end Solcore.Semantics
