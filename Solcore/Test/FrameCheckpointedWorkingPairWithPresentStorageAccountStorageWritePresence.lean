import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-! Compile-only regressions for proven-present total-write presence. -/

set_option autoImplicit false

namespace Tests

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Solcore.Core.Word) :
    (context.writeStorage slot Solcore.Core.Word.zero).storageAccount.storageValue?
        slot = none := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.storageValue?_writeStorage_zero
      context slot

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Solcore.Core.Word)
    (nonzero : value ≠ Solcore.Core.Word.zero) :
    (context.writeStorage slot value).storageAccount.storageValue? slot =
      some value := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.storageValue?_writeStorage_nonzero
      context slot value nonzero

end Tests
