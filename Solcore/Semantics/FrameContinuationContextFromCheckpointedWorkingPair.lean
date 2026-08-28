import Solcore.Semantics.FrameCheckpointedWorkingPair
import Solcore.Semantics.FrameContinuationContext

/-! Pure construction of continuation inputs from checkpointed working values. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameContinuationContext

universe u v w

/-- Build continuation inputs from checkpointed working values and an outcome. -/
def fromCheckpointedWorkingPair
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    FrameContinuationContext RollbackState TraceState TrapReason :=
  {
    stateCheckpoint := values.checkpoint.state
    effectCheckpoint := values.checkpoint.effects
    effectWorking := values.working.2
    result := ⟨values.working.1, outcome⟩
  }

end Solcore.Semantics.FrameContinuationContext
