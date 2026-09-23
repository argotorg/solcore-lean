import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteSparsePreservationProperties

/-! Compile-only regressions for distinct-slot sparse-storage preservation. -/

set_option autoImplicit false

namespace Tests

private example
    (account : Solcore.ContractRuntime.Account)
    (writtenSlot value otherSlot : Solcore.Core.Word)
    (different : otherSlot ≠ writtenSlot) :
    (account.storageWrite writtenSlot value).storageValue? otherSlot =
      account.storageValue? otherSlot := by
  exact Solcore.ContractRuntime.Account.storageValue?_storageWrite_other
    account writtenSlot value otherSlot different

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (writtenSlot value otherSlot : Solcore.Core.Word)
    (different : otherSlot ≠ writtenSlot) :
    (context.writeStorage writtenSlot value).storageAccount.storageValue?
        otherSlot =
      context.storageAccount.storageValue? otherSlot := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.storageValue?_writeStorage_other
      context writtenSlot value otherSlot different

end Tests
