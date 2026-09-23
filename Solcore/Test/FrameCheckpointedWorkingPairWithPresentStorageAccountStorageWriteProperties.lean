import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProperties
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountProperties

/-! Compile-only regressions for proven-present total-write coherence. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    context.context.writeStorage? slot value =
      some (context.writeStorage slot value).context := by
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.context_writeStorage?_eq_some_writeStorage_context
      context slot value

private example
    {RollbackState TraceState Result : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word)
    (observe :
      FrameCheckpointedWorkingPairWithStorageAddress
        RollbackState TraceState → Result) :
    (context.context.writeStorage? slot value).map observe =
      some (observe (context.writeStorage slot value).context) := by
  rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.context_writeStorage?_eq_some_writeStorage_context]
  rfl

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.context.writeStorage? slot value).bind
        FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount? =
      some (context.writeStorage slot value) := by
  rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.context_writeStorage?_eq_some_writeStorage_context]
  simp only [Option.bind_some]
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?_of_present
      (context.writeStorage slot value).context
      (context.writeStorage slot value).storageAccount
      (context.writeStorage slot value).storageAccount_present

end Tests
