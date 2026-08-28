import Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddressStorageRead
import Solcore.Semantics.WorldStateStorageReadWriteProperties

/-! Read-after-write laws for address-bound working storage. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- Reading the written slot observes the new value after a successful write. -/
@[simp] theorem readStorage?_writeStorage?_same
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.readStorage? slot) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => some value) := by
  simp [writeStorage?, FrameCheckpointedWorkingPair.writeWorkingStorage?,
    readStorage?, Function.comp_def]

/-- Writing another slot preserves the selected working-storage read. -/
@[simp] theorem readStorage?_writeStorage?_other_slot
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (context.writeStorage? writtenSlot value).map
        (fun next => next.readStorage? readSlot) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.readStorage? readSlot) := by
  simp [writeStorage?, FrameCheckpointedWorkingPair.writeWorkingStorage?,
    readStorage?, Function.comp_def, different]

end Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
