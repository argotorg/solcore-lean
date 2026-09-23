import Solcore.ContractRuntime.BalanceTransferCallFailure
import Solcore.ContractRuntime.CheckedCreationPreflight

/-! Stable call-result injection for checked creation preflight failures. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedCreationPreflightFailure

/-- Preserve existing call failures and append creation-specific failures. -/
def toContractCallFailure :
    CheckedCreationPreflightFailure → ContractCallFailure
  | .unavailable => .unavailable
  | .nonceOverflow => .nonceOverflow
  | .addressCollision => .addressCollision
  | .transfer failure => failure.toContractCallFailure

/-- Inject every preflight failure into the typed failed-result branch. -/
def toContractCallResult
    (failure : CheckedCreationPreflightFailure) :
    Core.ContractCallWordResult :=
  failure.toContractCallFailure.result

end Solcore.ContractRuntime.CheckedCreationPreflightFailure
