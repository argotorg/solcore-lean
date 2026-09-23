import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite
import Solcore.ContractRuntime.WorldStateProperties

/-! Non-selected working Account isolation for proven-present total writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- A total storage write preserves every non-selected working Account. -/
@[simp] theorem workingAccount?_writeStorage_other
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word)
    (otherAddress : Address)
    (different : otherAddress ≠ context.context.storageAddress) :
    (context.writeStorage slot value).context.values.working.1.account?
        otherAddress =
      context.context.values.working.1.account? otherAddress := by
  exact WorldState.account?_putAccount_other
    context.context.values.working.1 context.context.storageAddress otherAddress
    (context.storageAccount.storageWrite slot value) different

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
