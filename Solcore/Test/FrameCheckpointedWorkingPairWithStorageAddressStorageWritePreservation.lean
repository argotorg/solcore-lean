import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageWritePreservationProperties

/-! Compile-only regressions for retained-address storage-write preservation. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.storageAddress) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.storageAddress) := by
  simp

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (account : Account) (slot value : Core.Word)
    (present :
      context.values.working.1.account? context.storageAddress = some account) :
    (context.writeStorage? slot value).map
        (fun next => next.values.checkpoint) =
      some context.values.checkpoint := by
  rw [FrameCheckpointedWorkingPairWithStorageAddress.checkpoint_writeStorage?]
  simp [present]

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word)
    (absent :
      context.values.working.1.account? context.storageAddress = none) :
    (context.writeStorage? slot value).map
        (fun next => next.values.working.2) = none := by
  rw [FrameCheckpointedWorkingPairWithStorageAddress.workingEffects_writeStorage?]
  simp [absent]

end Tests
