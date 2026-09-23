import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteIsolationProperties

/-! Compile-only regressions for proven-present total-write isolation. -/

set_option autoImplicit false

namespace Tests

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Solcore.Core.Word)
    (otherAddress : Solcore.ContractRuntime.Address)
    (different : otherAddress ≠ context.context.storageAddress) :
    (context.writeStorage slot value).context.values.working.1.account?
        otherAddress =
      context.context.values.working.1.account? otherAddress := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.workingAccount?_writeStorage_other
      context slot value otherAddress different

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (firstSlot firstValue secondSlot secondValue : Solcore.Core.Word)
    (otherAddress : Solcore.ContractRuntime.Address)
    (different : otherAddress ≠ context.context.storageAddress) :
    ((context.writeStorage firstSlot firstValue).writeStorage
        secondSlot secondValue).context.values.working.1.account? otherAddress =
      context.context.values.working.1.account? otherAddress := by
  rw [
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.workingAccount?_writeStorage_other
      (context.writeStorage firstSlot firstValue)
      secondSlot secondValue otherAddress different,
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.workingAccount?_writeStorage_other
      context firstSlot firstValue otherAddress different]

end Tests
