import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-! Total storage reads from a proven-present selected working Account. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- Read one slot from the proven-present selected working Account. -/
def readStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Core.Word) : Core.Word :=
  context.storageAccount.storageRead slot

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
