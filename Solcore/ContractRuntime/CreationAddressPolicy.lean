import Solcore.ContractRuntime.RuntimeScalars

/-! Injected address derivation for contract creation. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/--
Policy boundary for deriving a created contract address from its creator and
the creator's pre-increment nonce. Concrete hashing remains outside semantics.
-/
structure CreationAddressPolicy where
  derive : Address → Core.Word → Address

end Solcore.ContractRuntime
