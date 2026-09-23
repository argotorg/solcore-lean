import Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccountProperties
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadWriteProperties

/-! Compile-only regressions for initialized present-storage refinement. -/

set_option autoImplicit false

namespace Tests

private example
    {RollbackState Event : Type}
    {parentWorking :
      Solcore.ContractRuntime.WorldState ×
        Solcore.ContractRuntime.FrameEffectJournal RollbackState
          (Solcore.ContractRuntime.FrameTrace Event)}
    (initialization :
      Solcore.ContractRuntime.ParentIndexedFrameInitialization
        RollbackState Event parentWorking)
    (storageAddress : Solcore.ContractRuntime.Address)
    (absent :
      initialization.initialWorld.account? storageAddress = none) :
    initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress = none := by
  exact
    Solcore.ContractRuntime.ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?_of_absent
      initialization storageAddress absent

private example
    {RollbackState Event : Type}
    {parentWorking :
      Solcore.ContractRuntime.WorldState ×
        Solcore.ContractRuntime.FrameEffectJournal RollbackState
          (Solcore.ContractRuntime.FrameTrace Event)}
    (initialization :
      Solcore.ContractRuntime.ParentIndexedFrameInitialization
        RollbackState Event parentWorking)
    (storageAddress : Solcore.ContractRuntime.Address)
    (account : Solcore.ContractRuntime.Account)
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
    Solcore.ContractRuntime.ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
      initialization storageAddress account present

private example
    {RollbackState Event : Type}
    {parentWorking :
      Solcore.ContractRuntime.WorldState ×
        Solcore.ContractRuntime.FrameEffectJournal RollbackState
          (Solcore.ContractRuntime.FrameTrace Event)}
    (initialization :
      Solcore.ContractRuntime.ParentIndexedFrameInitialization
        RollbackState Event parentWorking)
    (storageAddress : Solcore.ContractRuntime.Address)
    (account : Solcore.ContractRuntime.Account)
    (present :
      initialization.initialWorld.account? storageAddress = some account)
    (slot value : Solcore.Core.Word) :
    (initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress).map
        (fun context =>
          (context.writeStorage slot value).readStorage slot) =
      some value := by
  rw [
    Solcore.ContractRuntime.ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
      initialization storageAddress account present]
  exact
    congrArg some
      (Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_same
        ⟨initialization.toCheckpointedWorkingPairWithStorageAddress
            storageAddress,
          account,
          present⟩
        slot value)

end Tests
