import Solcore.ContractRuntime.FrameCheckpointSnapshot

/-! Structural pairing of one frame checkpoint with independent working values. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

/-- One checkpoint snapshot paired with independent state-and-effects working values. -/
structure FrameCheckpointedWorkingPair
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  checkpoint : FrameCheckpointSnapshot RollbackState TraceState
  working : WorldState × FrameEffectJournal RollbackState TraceState

end Solcore.ContractRuntime
