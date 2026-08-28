import Solcore.Semantics.FrameCheckpointSnapshot

/-! Definitional projections of nominal frame checkpoint snapshots. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameCheckpointSnapshot

universe u v

/-- Constructing a snapshot retains the caller-supplied state exactly. -/
@[simp] theorem state_fromWorkingPair
    {RollbackState : Type u} {TraceState : Type v}
    (working : WorldState × FrameEffectJournal RollbackState TraceState) :
    (fromWorkingPair working).state = working.1 := by
  rfl

/-- Constructing a snapshot retains the caller-supplied effects exactly. -/
@[simp] theorem effects_fromWorkingPair
    {RollbackState : Type u} {TraceState : Type v}
    (working : WorldState × FrameEffectJournal RollbackState TraceState) :
    (fromWorkingPair working).effects = working.2 := by
  rfl

end Solcore.Semantics.FrameCheckpointSnapshot
