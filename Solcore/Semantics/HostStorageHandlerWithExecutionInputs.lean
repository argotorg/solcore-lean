import Solcore.Semantics.HostStorageExecutionInputs
import Solcore.Semantics.HostStorageHandler

/-! Explicit-input migration seam for combined storage request handling. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver

universe u v

/-- Handle one current request using the code selector in the run-fixed input. -/
def handleRequestWithInputs
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (request : Core.HostRequest) :
    Context RollbackState TraceState × request.Response :=
  handleRequest inputs.codeAddress context request

/-- Current combined handler indexed by the complete run-fixed input. -/
def handlerWithInputs
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs) :
    HostHandler (Context RollbackState TraceState) :=
  handler inputs.codeAddress

/-- Handle one suspension using the complete run-fixed input. -/
def handleSuspensionWithInputs
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    Context RollbackState TraceState × Core.State :=
  handleSuspension inputs.codeAddress context suspension

end Solcore.Semantics.HostStorageDriver
