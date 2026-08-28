import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteSparsePreservationProperties

/-! Compile-only regressions for distinct-slot sparse-storage preservation. -/

set_option autoImplicit false

namespace Tests

private example
    (account : Solcore.Semantics.Account)
    (writtenSlot value otherSlot : Solcore.Core.Word)
    (different : otherSlot ≠ writtenSlot) :
    (account.storageWrite writtenSlot value).storageValue? otherSlot =
      account.storageValue? otherSlot := by
  exact Solcore.Semantics.Account.storageValue?_storageWrite_other
    account writtenSlot value otherSlot different

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (writtenSlot value otherSlot : Solcore.Core.Word)
    (different : otherSlot ≠ writtenSlot) :
    (context.writeStorage writtenSlot value).storageAccount.storageValue?
        otherSlot =
      context.storageAccount.storageValue? otherSlot := by
  exact
    Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount.storageValue?_writeStorage_other
      context writtenSlot value otherSlot different

end Tests
