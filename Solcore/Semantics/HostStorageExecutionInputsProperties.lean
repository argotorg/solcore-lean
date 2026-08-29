import Solcore.Semantics.HostStorageExecutionInputs

/-! Exact projections of immutable combined-storage execution inputs. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver

@[simp] theorem ExecutionInputs.mk_codeAddress
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address) :
    (ExecutionInputs.mk codeAddress callValue callerAddress).codeAddress =
      codeAddress :=
  rfl

@[simp] theorem ExecutionInputs.mk_callValue
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address) :
    (ExecutionInputs.mk codeAddress callValue callerAddress).callValue = callValue :=
  rfl

@[simp] theorem ExecutionInputs.mk_callerAddress
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address) :
    (ExecutionInputs.mk codeAddress callValue callerAddress).callerAddress =
      callerAddress :=
  rfl

end Solcore.Semantics.HostStorageDriver
