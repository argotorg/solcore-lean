import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteAlgebraProperties

/-! Compile-only regressions for proven-present total write algebra. -/

set_option autoImplicit false

namespace Tests

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot first second : Solcore.Core.Word) :
    (context.writeStorage slot first).writeStorage slot second =
      context.writeStorage slot second := by
  exact
    Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount.writeStorage_overwrite
      context slot first second

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (leftSlot leftValue rightSlot rightValue : Solcore.Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (context.writeStorage leftSlot leftValue).writeStorage
        rightSlot rightValue =
      (context.writeStorage rightSlot rightValue).writeStorage
        leftSlot leftValue := by
  exact
    Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount.writeStorage_commute_slots
      context leftSlot leftValue rightSlot rightValue different

end Tests
