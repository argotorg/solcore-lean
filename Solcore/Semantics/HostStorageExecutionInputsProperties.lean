import Solcore.Semantics.HostStorageExecutionInputs

/-! Exact projections of immutable combined-storage execution inputs. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver

@[simp] theorem ExecutionInputs.mk_codeAddress
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address)
    (inputData : InputData) (currentAddress : Address) :
    (ExecutionInputs.mk codeAddress callValue callerAddress inputData
      currentAddress).codeAddress =
      codeAddress :=
  rfl

@[simp] theorem ExecutionInputs.mk_callValue
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address)
    (inputData : InputData) (currentAddress : Address) :
    (ExecutionInputs.mk codeAddress callValue callerAddress inputData
      currentAddress).callValue =
      callValue :=
  rfl

@[simp] theorem ExecutionInputs.mk_callerAddress
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address)
    (inputData : InputData) (currentAddress : Address) :
    (ExecutionInputs.mk codeAddress callValue callerAddress inputData
      currentAddress).callerAddress =
      callerAddress :=
  rfl

@[simp] theorem ExecutionInputs.mk_inputData
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address)
    (inputData : InputData) (currentAddress : Address) :
    (ExecutionInputs.mk codeAddress callValue callerAddress inputData
      currentAddress).inputData =
      inputData :=
  rfl

@[simp] theorem ExecutionInputs.mk_currentAddress
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address)
    (inputData : InputData) (currentAddress : Address) :
    (ExecutionInputs.mk codeAddress callValue callerAddress inputData
      currentAddress).currentAddress = currentAddress :=
  rfl

end Solcore.Semantics.HostStorageDriver
