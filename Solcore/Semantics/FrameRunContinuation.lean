import Solcore.Semantics.FrameRunEffectResolution

/-! Caller-owned continuation after synchronized frame resolution. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameRunResult

universe u v w x

/-- Resolve caller-supplied state and effects before invoking a continuation. -/
def continueWithResolvedStateAndEffects?
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    Option Next :=
  (result.resolvedWorldStateAndEffects?
    stateCheckpoint effectCheckpoint effectWorking).bind next

end Solcore.Semantics.FrameRunResult
