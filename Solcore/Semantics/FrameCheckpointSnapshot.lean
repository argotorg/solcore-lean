import Solcore.Semantics.FrameEffectJournal
import Solcore.Semantics.WorldState

/-! Nominal representation of caller-supplied synchronized checkpoint values. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

/-- Caller-designated synchronized values represented as a frame checkpoint. -/
structure FrameCheckpointSnapshot
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  state : WorldState
  effects : FrameEffectJournal RollbackState TraceState

namespace FrameCheckpointSnapshot

/-- Represent one caller-supplied synchronized working pair as a checkpoint. -/
def fromWorkingPair
    {RollbackState : Type u} {TraceState : Type v}
    (working : WorldState × FrameEffectJournal RollbackState TraceState) :
    FrameCheckpointSnapshot RollbackState TraceState :=
  ⟨working.1, working.2⟩

end FrameCheckpointSnapshot

end Solcore.Semantics
