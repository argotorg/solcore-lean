import Solcore.Semantics.AddressWordBridge

/-! Immutable inputs shared by one combined handled storage execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver

/-- Run-fixed inputs kept outside the mutable working-storage context. -/
structure ExecutionInputs where
  codeAddress : Address
  callValue : Core.Word

end Solcore.Semantics.HostStorageDriver
