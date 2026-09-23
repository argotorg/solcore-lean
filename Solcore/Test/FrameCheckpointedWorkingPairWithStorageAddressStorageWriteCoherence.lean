import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageWriteCoherenceProperties

/-! Compile-only regressions for retained-address write values coherence. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map (fun next => next.values) =
      context.values.writeWorkingStorage?
        context.storageAddress slot value := by
  simp

private example
    {RollbackState TraceState Result : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word)
    (observe :
      FrameCheckpointedWorkingPair RollbackState TraceState → Result) :
    (context.writeStorage? slot value).map
        (fun next => observe next.values) =
      (context.values.writeWorkingStorage?
        context.storageAddress slot value).map observe := by
  change (context.writeStorage? slot value).map
      (observe ∘ fun next => next.values) = _
  rw [← Option.map_map]
  rw [FrameCheckpointedWorkingPairWithStorageAddress.values_writeStorage?]

end Tests
