import Solcore.ContractRuntime.AddressWordBridge
import Solcore.ContractRuntime.HostStorageInputData

/-! Immutable inputs shared by one combined handled storage execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver

/-- Run-fixed inputs kept outside the mutable working-storage context. -/
structure ExecutionInputs where
  codeAddress : Address
  callValue : Core.Word
  callerAddress : Address
  inputData : InputData
  currentAddress : Address

end Solcore.ContractRuntime.HostStorageDriver

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageExecutionInputsProperties`
-/

/-! Exact projections of immutable combined-storage execution inputs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver

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

end Solcore.ContractRuntime.HostStorageDriver
