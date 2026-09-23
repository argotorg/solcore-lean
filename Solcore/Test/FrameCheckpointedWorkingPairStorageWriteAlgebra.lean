import Solcore.ContractRuntime.FrameCheckpointedWorkingPairStorageWriteAlgebraProperties

/-! Compile-only regressions for checkpointed working storage-write algebra. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    {RollbackState TraceState : Type}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address) (slot first second : Core.Word) :
    (values.writeWorkingStorage? address slot first).bind
        (fun next => next.writeWorkingStorage? address slot second) =
      values.writeWorkingStorage? address slot second := by
  exact FrameCheckpointedWorkingPair.writeWorkingStorage?_overwrite
    values address slot first second

private example
    {RollbackState TraceState : Type}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (values.writeWorkingStorage? address leftSlot leftValue).bind
        (fun next =>
          next.writeWorkingStorage? address rightSlot rightValue) =
      (values.writeWorkingStorage? address rightSlot rightValue).bind
        (fun next =>
          next.writeWorkingStorage? address leftSlot leftValue) := by
  exact FrameCheckpointedWorkingPair.writeWorkingStorage?_commute_slots
    values address leftSlot leftValue rightSlot rightValue different

private example
    {RollbackState TraceState : Type}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (leftAddress rightAddress : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftAddress ≠ rightAddress) :
    (values.writeWorkingStorage? leftAddress leftSlot leftValue).bind
        (fun next =>
          next.writeWorkingStorage? rightAddress rightSlot rightValue) =
      (values.writeWorkingStorage? rightAddress rightSlot rightValue).bind
        (fun next =>
          next.writeWorkingStorage? leftAddress leftSlot leftValue) := by
  exact FrameCheckpointedWorkingPair.writeWorkingStorage?_commute_addresses
    values leftAddress rightAddress leftSlot leftValue rightSlot rightValue
      different

end Tests
