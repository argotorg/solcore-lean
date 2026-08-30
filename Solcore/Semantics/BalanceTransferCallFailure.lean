import Solcore.Semantics.BalanceTransfer
import Solcore.Semantics.ContractCallFailure

/-! Stable checked-call failures for total balance-transfer failures. -/

set_option autoImplicit false

namespace Solcore.Semantics

namespace BalanceTransferFailure

/-- Translate every checked transfer failure into the public call failure ABI. -/
def toContractCallFailure : BalanceTransferFailure → ContractCallFailure
  | .senderAbsent => .unavailable
  | .recipientAbsent => .unavailable
  | .insufficientBalance => .insufficientBalance
  | .recipientOverflow => .balanceOverflow

/-- Inject a checked transfer failure into the typed contract-call result. -/
def toContractCallResult
    (failure : BalanceTransferFailure) : Core.ContractCallWordResult :=
  failure.toContractCallFailure.result

end BalanceTransferFailure

end Solcore.Semantics
