import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecution
import Solcore.Semantics.HostStorageDriverWithExecutionInputs

/-! Address-selected handled execution with one immutable execution input. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace FrameCheckpointedWorkingPairWithPresentStorageAccount

/-- Select and run code using the same immutable code selector and call input. -/
def runCodeWithStorageWithInputs?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    Option
      (HostDriverResult
        (HostStorageDriver.Context RollbackState TraceState)) :=
  (context.context.values.working.1.code? inputs.codeAddress).map fun code =>
    code.runWithStorageInputs context inputs fuel

end FrameCheckpointedWorkingPairWithPresentStorageAccount

end Solcore.Semantics
