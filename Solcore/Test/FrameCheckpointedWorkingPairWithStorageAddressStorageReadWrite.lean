import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-! Compile-only regressions for address-bound storage read/write laws. -/

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
        (fun next => next.readStorage? slot) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => some value) := by
  simp

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (context.writeStorage? writtenSlot value).map
        (fun next => next.readStorage? readSlot) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.readStorage? readSlot) := by
  simp [different]

end Tests
