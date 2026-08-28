import Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddressProperties

/-! Stage-preserving structural observations of address-bound storage writes. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- A conditional write retains the exact stored address in its success branch. -/
@[simp] theorem storageAddress_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.storageAddress) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.storageAddress) := by
  cases present :
      context.values.working.1.account? context.storageAddress <;>
    simp [present]

/-- A conditional write retains the exact checkpoint in its success branch. -/
@[simp] theorem checkpoint_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.values.checkpoint) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.values.checkpoint) := by
  cases present :
      context.values.working.1.account? context.storageAddress <;>
    simp [present]

/-- A conditional write retains the exact working effects in its success branch. -/
@[simp] theorem workingEffects_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.values.working.2) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.values.working.2) := by
  cases present :
      context.values.working.1.account? context.storageAddress <;>
    simp [present]

end Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
