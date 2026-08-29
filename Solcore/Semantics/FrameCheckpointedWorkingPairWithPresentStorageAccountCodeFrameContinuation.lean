import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecution
import Solcore.Semantics.HostDriverFrameContinuation

/-! Frame-continuation construction after address-selected handled execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v w

namespace FrameCheckpointedWorkingPairWithPresentStorageAccount

/--
Select checked code and build continuation inputs only when its handled run
completes. The outer option records code selection; the inner option records
whether the selected execution completed within its fuel budget.
-/
def runCodeWithStorageContinuationContext?
    {RollbackState : Type u}
    {TraceState : Type v}
    {TrapReason : Type w}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option
      (Option
        (FrameContinuationContext RollbackState TraceState TrapReason)) :=
  (context.runCodeWithStorage? codeAddress fuel).map fun result =>
    result.toFrameContinuationContext?
      (fun current => current.context.values) doneOutcome

end FrameCheckpointedWorkingPairWithPresentStorageAccount

end Solcore.Semantics
