import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProjectionProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteIsolationProperties

/-! Compile-only regressions for proven-present total-write projections. -/

set_option autoImplicit false

namespace Tests

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Solcore.Core.Word) :
    (context.writeStorage slot value).context.storageAddress =
      context.context.storageAddress := by
  exact
    Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount.storageAddress_writeStorage
      context slot value

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Solcore.Core.Word) :
    (context.writeStorage slot value).context.values.checkpoint =
      context.context.values.checkpoint := by
  exact
    Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount.checkpoint_writeStorage
      context slot value

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Solcore.Core.Word) :
    (context.writeStorage slot value).context.values.working.2 =
      context.context.values.working.2 := by
  exact
    Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount.workingEffects_writeStorage
      context slot value

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Solcore.Core.Word) :
    (context.writeStorage slot value).storageAccount =
      context.storageAccount.storageWrite slot value := by
  exact
    Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount.storageAccount_writeStorage
      context slot value

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (firstSlot firstValue secondSlot secondValue : Solcore.Core.Word)
    (otherAddress : Solcore.Semantics.Address)
    (different : otherAddress ≠ context.context.storageAddress) :
    ((context.writeStorage firstSlot firstValue).writeStorage
        secondSlot secondValue).context.values.working.1.account? otherAddress =
      context.context.values.working.1.account? otherAddress := by
  simp [different]

end Tests
