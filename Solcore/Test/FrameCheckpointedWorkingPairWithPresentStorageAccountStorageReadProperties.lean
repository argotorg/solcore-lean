import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-! Compile-only regressions for proven-present total-read coherence. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Core.Word) :
    context.context.readStorage? slot = some (context.readStorage slot) := by
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.context_readStorage?_eq_some_readStorage
      context slot

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot fallback : Core.Word) :
    (context.context.readStorage? slot).getD fallback =
      context.readStorage slot := by
  rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.context_readStorage?_eq_some_readStorage]
  rfl

end Tests
