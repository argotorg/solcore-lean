import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProjectionProperties
import Solcore.ContractRuntime.WorldStateProperties

/-! Sparse storage presence after proven-present total writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- Writing zero removes the selected sparse-storage entry. -/
theorem storageValue?_writeStorage_zero
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Core.Word) :
    (context.writeStorage slot Core.Word.zero).storageAccount.storageValue?
        slot = none := by
  rw [storageAccount_writeStorage]
  exact Account.storageValue?_storageWrite_zero context.storageAccount slot

/-- Writing a nonzero word creates the corresponding sparse-storage entry. -/
theorem storageValue?_writeStorage_nonzero
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word)
    (nonzero : value ≠ Core.Word.zero) :
    (context.writeStorage slot value).storageAccount.storageValue? slot =
      some value := by
  rw [storageAccount_writeStorage]
  exact Account.storageValue?_storageWrite_nonzero
    context.storageAccount slot value nonzero

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
