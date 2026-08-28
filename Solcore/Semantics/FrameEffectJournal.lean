import Solcore.Semantics.FrameOutcome

/-! Generic rollback-scoped state and revert-surviving trace policy. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v w

/-- Opaque rollback-scoped state paired with an accumulated trace snapshot. -/
structure FrameEffectJournal
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  rollback : RollbackState
  trace : TraceState

namespace FrameEffectJournal

/-- Resolve return and revert journals while leaving trap disposition open. -/
def resolved?
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (checkpoint working : FrameEffectJournal RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    Option (FrameEffectJournal RollbackState TraceState) :=
  match outcome with
  | .returned _ => some working
  | .reverted _ => some ⟨checkpoint.rollback, working.trace⟩
  | .trapped _ => none

end FrameEffectJournal

end Solcore.Semantics
