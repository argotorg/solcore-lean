import Solcore.Semantics.HostStorageExecutionInputs

/-! Exact projections of immutable combined-storage execution inputs. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver

@[simp] theorem ExecutionInputs.mk_codeAddress
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address)
    (inputData : InputData) :
    (ExecutionInputs.mk codeAddress callValue callerAddress inputData).codeAddress =
      codeAddress :=
  rfl

@[simp] theorem ExecutionInputs.mk_callValue
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address)
    (inputData : InputData) :
    (ExecutionInputs.mk codeAddress callValue callerAddress inputData).callValue =
      callValue :=
  rfl

@[simp] theorem ExecutionInputs.mk_callerAddress
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address)
    (inputData : InputData) :
    (ExecutionInputs.mk codeAddress callValue callerAddress inputData).callerAddress =
      callerAddress :=
  rfl

@[simp] theorem ExecutionInputs.mk_inputData
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address)
    (inputData : InputData) :
    (ExecutionInputs.mk codeAddress callValue callerAddress inputData).inputData =
      inputData :=
  rfl

end Solcore.Semantics.HostStorageDriver
