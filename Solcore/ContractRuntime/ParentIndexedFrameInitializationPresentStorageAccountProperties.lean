import Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccount
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountProperties

/-! Branch laws for parent-indexed initialization storage refinement. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v

/-- An absent Account keeps the initialization refinement unavailable. -/
@[simp] theorem
    toCheckpointedWorkingPairWithPresentStorageAccount?_of_absent
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (absent :
      initialization.initialWorld.account? storageAddress = none) :
    initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress = none := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?_of_absent
      (initialization.toCheckpointedWorkingPairWithStorageAddress storageAddress)
      absent

/-- A present Account returns its exact initialized evidence carrier. -/
@[simp] theorem
    toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (account : Account)
    (present :
      initialization.initialWorld.account? storageAddress = some account) :
    initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress =
      some
        ⟨initialization.toCheckpointedWorkingPairWithStorageAddress
            storageAddress,
          account,
          present⟩ := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?_of_present
      (initialization.toCheckpointedWorkingPairWithStorageAddress storageAddress)
      account present

end Solcore.ContractRuntime.ParentIndexedFrameInitialization
