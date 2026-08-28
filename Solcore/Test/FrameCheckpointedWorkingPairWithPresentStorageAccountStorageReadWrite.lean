import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadWriteProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadProperties

/-! Compile-only regressions for proven-present total read/write coherence. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).readStorage slot = value := by
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_same
      context slot value

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (context.writeStorage writtenSlot value).readStorage readSlot =
      context.readStorage readSlot := by
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_other
      context writtenSlot value readSlot different

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).context.readStorage? slot =
      some value := by
  rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.context_readStorage?_eq_some_readStorage]
  rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_same]

end Tests
