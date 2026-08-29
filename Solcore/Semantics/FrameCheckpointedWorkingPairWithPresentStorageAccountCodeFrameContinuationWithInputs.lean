import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionWithInputs
import Solcore.Semantics.HostDriverFrameContinuation

/-! Frame-continuation construction with one immutable execution input. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v w

namespace FrameCheckpointedWorkingPairWithPresentStorageAccount

/-- Preserve selection and completion as separate optional boundaries. -/
def runCodeWithStorageContinuationContext?
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option
      (Option
        (FrameContinuationContext RollbackState TraceState TrapReason)) :=
  (context.runCodeWithStorage? inputs fuel).map fun result =>
    result.toFrameContinuationContext?
      (fun current => current.context.values) doneOutcome

end FrameCheckpointedWorkingPairWithPresentStorageAccount

end Solcore.Semantics
