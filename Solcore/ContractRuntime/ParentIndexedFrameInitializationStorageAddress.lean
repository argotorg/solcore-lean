import Solcore.ContractRuntime.ParentIndexedFrameInitialization
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-! Canonical storage-address wiring for parent-indexed initialization. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v

/-- Bind one storage selector to the initialized checkpointed working values. -/
def toCheckpointedWorkingPairWithStorageAddress
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    FrameCheckpointedWorkingPairWithStorageAddress
      RollbackState (FrameTrace Event) :=
  ⟨storageAddress, initialization.toCheckpointedWorkingPair⟩

end Solcore.ContractRuntime.ParentIndexedFrameInitialization
