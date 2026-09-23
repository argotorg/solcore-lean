import Solcore.ContractRuntime.ParentIndexedFrameInitializationStorageAddress

/-! Projection laws for storage-address initialization wiring. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v

@[simp] theorem
    storageAddress_toCheckpointedWorkingPairWithStorageAddress
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    (initialization.toCheckpointedWorkingPairWithStorageAddress
      storageAddress).storageAddress = storageAddress := by
  rfl

@[simp] theorem values_toCheckpointedWorkingPairWithStorageAddress
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    (initialization.toCheckpointedWorkingPairWithStorageAddress
      storageAddress).values = initialization.toCheckpointedWorkingPair := by
  rfl

end Solcore.ContractRuntime.ParentIndexedFrameInitialization
