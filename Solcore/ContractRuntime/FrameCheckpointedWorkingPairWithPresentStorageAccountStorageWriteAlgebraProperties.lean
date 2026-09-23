import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite
import Solcore.ContractRuntime.WorldStateUpdateAlgebraProperties

/-! Algebraic laws for proven-present total working-storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- A later total write to the same slot supersedes the earlier write. -/
@[simp] theorem writeStorage_overwrite
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot first second : Core.Word) :
    (context.writeStorage slot first).writeStorage slot second =
      context.writeStorage slot second := by
  simp [writeStorage]

/-- Total writes to distinct slots commute. -/
theorem writeStorage_commute_slots
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (context.writeStorage leftSlot leftValue).writeStorage
        rightSlot rightValue =
      (context.writeStorage rightSlot rightValue).writeStorage
        leftSlot leftValue := by
  simp [writeStorage,
    Account.storageWrite_commute context.storageAccount
      leftSlot leftValue rightSlot rightValue different]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
