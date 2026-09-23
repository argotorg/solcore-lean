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
