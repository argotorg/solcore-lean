import Solcore.Semantics.HostStorageDriver
import Solcore.Semantics.HostStorageHandlerWithExecutionInputs

/-! Explicit-input migration seam for combined handled storage execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace HostStorageDriver

/-- Run the current handler using one immutable execution input. -/
def runWithInputs
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    HostDriverResult (Context RollbackState TraceState) :=
  run context inputs.codeAddress fuel state

end HostStorageDriver

namespace CheckedHostCoreProgram

/-- Start checked code with one immutable execution input. -/
def runWithStorageInputs
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    HostDriverResult
      (HostStorageDriver.Context RollbackState TraceState) :=
  code.runWithStorage context inputs.codeAddress fuel

end CheckedHostCoreProgram

end Solcore.Semantics
