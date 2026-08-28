import Solcore.Semantics.ParentIndexedFrameInitializationStorageAddressProperties

/-! Compile-only regressions for storage-address initialization wiring. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

private example
    {RollbackState Event : Type}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    (initialization.toCheckpointedWorkingPairWithStorageAddress
      storageAddress).storageAddress = storageAddress := by
  simp

private example
    {RollbackState Event : Type}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    (initialization.toCheckpointedWorkingPairWithStorageAddress
      storageAddress).values = initialization.toCheckpointedWorkingPair := by
  simp

private example
    {RollbackState Event : Type}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) (slot value : Core.Word) :
    (initialization.toCheckpointedWorkingPairWithStorageAddress
      storageAddress).writeStorage? slot value =
      (initialization.toCheckpointedWorkingPair.writeWorkingStorage?
        storageAddress slot value).map fun values =>
          ⟨storageAddress, values⟩ := by
  simp only [FrameCheckpointedWorkingPairWithStorageAddress.writeStorage?,
    ParentIndexedFrameInitialization.storageAddress_toCheckpointedWorkingPairWithStorageAddress,
    ParentIndexedFrameInitialization.values_toCheckpointedWorkingPairWithStorageAddress]

end Tests
