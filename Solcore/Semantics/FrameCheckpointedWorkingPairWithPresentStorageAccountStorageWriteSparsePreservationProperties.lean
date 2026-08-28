import Solcore.Semantics.AccountStorageWriteSparsePreservationProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProjectionProperties

/-! Distinct-slot sparse-storage preservation for proven-present total writes. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- A total write preserves the optional sparse entry at every other slot. -/
theorem storageValue?_writeStorage_other
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (writtenSlot value otherSlot : Core.Word)
    (different : otherSlot ≠ writtenSlot) :
    (context.writeStorage writtenSlot value).storageAccount.storageValue?
        otherSlot =
      context.storageAccount.storageValue? otherSlot := by
  rw [storageAccount_writeStorage]
  exact Account.storageValue?_storageWrite_other
    context.storageAccount writtenSlot value otherSlot different

end Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
