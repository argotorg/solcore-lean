import Solcore.Semantics.HostStorageExecutionInputs

/-! Exact projections of immutable combined-storage execution inputs. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver

@[simp] theorem ExecutionInputs.mk_codeAddress
    (codeAddress : Address) (callValue : Core.Word) :
    (ExecutionInputs.mk codeAddress callValue).codeAddress = codeAddress :=
  rfl

@[simp] theorem ExecutionInputs.mk_callValue
    (codeAddress : Address) (callValue : Core.Word) :
    (ExecutionInputs.mk codeAddress callValue).callValue = callValue :=
  rfl

end Solcore.Semantics.HostStorageDriver
