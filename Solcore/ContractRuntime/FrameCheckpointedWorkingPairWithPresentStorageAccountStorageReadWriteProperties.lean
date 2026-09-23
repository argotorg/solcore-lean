import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageRead
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite
import Solcore.ContractRuntime.WorldStateProperties

/-! Read-after-write laws for proven-present total working storage. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- Reading the written slot observes the new total-write value. -/
@[simp] theorem readStorage_writeStorage_same
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).readStorage slot = value := by
  exact Account.storageRead_storageWrite_same
    context.storageAccount slot value

/-- A total write to another slot preserves the prior total read. -/
@[simp] theorem readStorage_writeStorage_other
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (context.writeStorage writtenSlot value).readStorage readSlot =
      context.readStorage readSlot := by
  exact Account.storageRead_storageWrite_other
    context.storageAccount writtenSlot value readSlot different

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
