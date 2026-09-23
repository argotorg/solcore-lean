import Solcore.ContractRuntime.FrameCheckpointedWorkingPair

/-! Working-world storage writes for checkpointed frame values. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPair

universe u v

/-- Conditionally update storage in only the working world state. -/
def writeWorkingStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address) (slot value : Core.Word) :
    Option (FrameCheckpointedWorkingPair RollbackState TraceState) :=
  (values.working.1.writeStorage? address slot value).map fun state =>
    ⟨values.checkpoint, (state, values.working.2)⟩

end Solcore.ContractRuntime.FrameCheckpointedWorkingPair
