import Solcore.ContractRuntime.ParentIndexedFrameInitializationStorageAddress
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-! Present-storage refinement for parent-indexed initialization. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v

/-- Refine the initialized storage selector exactly when its Account exists. -/
def toCheckpointedWorkingPairWithPresentStorageAccount?
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    Option
      (FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState (FrameTrace Event)) :=
  (initialization.toCheckpointedWorkingPairWithStorageAddress
    storageAddress).withPresentStorageAccount?

end Solcore.ContractRuntime.ParentIndexedFrameInitialization
