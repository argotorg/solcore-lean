import Solcore.Semantics.ParentIndexedFrameInitializationPresentStorageAccountProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadWriteProperties

/-! Compile-only regressions for initialized present-storage refinement. -/

set_option autoImplicit false

namespace Tests

private example
    {RollbackState Event : Type}
    {parentWorking :
      Solcore.Semantics.WorldState ×
        Solcore.Semantics.FrameEffectJournal RollbackState
          (Solcore.Semantics.FrameTrace Event)}
    (initialization :
      Solcore.Semantics.ParentIndexedFrameInitialization
        RollbackState Event parentWorking)
    (storageAddress : Solcore.Semantics.Address)
    (absent :
      initialization.initialWorld.account? storageAddress = none) :
    initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress = none := by
  exact
    Solcore.Semantics.ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?_of_absent
      initialization storageAddress absent

private example
    {RollbackState Event : Type}
    {parentWorking :
      Solcore.Semantics.WorldState ×
        Solcore.Semantics.FrameEffectJournal RollbackState
          (Solcore.Semantics.FrameTrace Event)}
    (initialization :
      Solcore.Semantics.ParentIndexedFrameInitialization
        RollbackState Event parentWorking)
    (storageAddress : Solcore.Semantics.Address)
    (account : Solcore.Semantics.Account)
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
    Solcore.Semantics.ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
      initialization storageAddress account present

private example
    {RollbackState Event : Type}
    {parentWorking :
      Solcore.Semantics.WorldState ×
        Solcore.Semantics.FrameEffectJournal RollbackState
          (Solcore.Semantics.FrameTrace Event)}
    (initialization :
      Solcore.Semantics.ParentIndexedFrameInitialization
        RollbackState Event parentWorking)
    (storageAddress : Solcore.Semantics.Address)
    (account : Solcore.Semantics.Account)
    (present :
      initialization.initialWorld.account? storageAddress = some account)
    (slot value : Solcore.Core.Word) :
    (initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress).map
        (fun context =>
          (context.writeStorage slot value).readStorage slot) =
      some value := by
  rw [
    Solcore.Semantics.ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
      initialization storageAddress account present]
  exact
    congrArg some
      (Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_same
        ⟨initialization.toCheckpointedWorkingPairWithStorageAddress
            storageAddress,
          account,
          present⟩
        slot value)

end Tests
