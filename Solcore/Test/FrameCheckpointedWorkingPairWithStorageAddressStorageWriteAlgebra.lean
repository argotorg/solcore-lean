import Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddressStorageWriteAlgebraProperties

/-! Compile-only regressions for retained-address storage-write algebra. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot first second : Core.Word) :
    (context.writeStorage? slot first).bind
        (fun next => next.writeStorage? slot second) =
      context.writeStorage? slot second := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.writeStorage?_overwrite
      context slot first second

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (context.writeStorage? leftSlot leftValue).bind
        (fun next => next.writeStorage? rightSlot rightValue) =
      (context.writeStorage? rightSlot rightValue).bind
        (fun next => next.writeStorage? leftSlot leftValue) := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.writeStorage?_commute_slots
      context leftSlot leftValue rightSlot rightValue different

end Tests
