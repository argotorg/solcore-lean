import Solcore.Semantics.FrameCheckpointedWorkingPairStorageWrite

/-! A caller-addressed storage boundary over checkpointed working values. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

/-- A checkpointed working pair with one caller-supplied storage address. -/
structure FrameCheckpointedWorkingPairWithStorageAddress
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  storageAddress : Address
  values : FrameCheckpointedWorkingPair RollbackState TraceState

namespace FrameCheckpointedWorkingPairWithStorageAddress

/-- Write one slot at the stored address in only the working world state. -/
def writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    Option
      (FrameCheckpointedWorkingPairWithStorageAddress
        RollbackState TraceState) :=
  (context.values.writeWorkingStorage?
    context.storageAddress slot value).map fun values =>
      ⟨context.storageAddress, values⟩

end FrameCheckpointedWorkingPairWithStorageAddress

end Solcore.Semantics
