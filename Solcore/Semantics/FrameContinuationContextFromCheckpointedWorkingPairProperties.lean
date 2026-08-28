import Solcore.Semantics.FrameContinuationContextFromCheckpointedWorkingPair

/-! Projections of continuation contexts built from checkpointed working values. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameContinuationContext

universe u v w

/-- Construction retains the checkpoint state exactly. -/
@[simp] theorem stateCheckpoint_fromCheckpointedWorkingPair
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    (fromCheckpointedWorkingPair values outcome).stateCheckpoint =
      values.checkpoint.state := by
  rfl

/-- Construction retains the checkpoint effects exactly. -/
@[simp] theorem effectCheckpoint_fromCheckpointedWorkingPair
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    (fromCheckpointedWorkingPair values outcome).effectCheckpoint =
      values.checkpoint.effects := by
  rfl

/-- Construction retains the working effects exactly. -/
@[simp] theorem effectWorking_fromCheckpointedWorkingPair
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    (fromCheckpointedWorkingPair values outcome).effectWorking =
      values.working.2 := by
  rfl

/-- Construction pairs the working state with the supplied outcome exactly. -/
@[simp] theorem result_fromCheckpointedWorkingPair
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    (fromCheckpointedWorkingPair values outcome).result =
      ⟨values.working.1, outcome⟩ := by
  rfl

end Solcore.Semantics.FrameContinuationContext
