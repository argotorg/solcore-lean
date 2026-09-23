import Solcore.ContractRuntime.BalanceTransferCallFailure
import Solcore.ContractRuntime.ContractCallFailureProperties

/-! Exact failure translation laws for value-bearing checked calls. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.BalanceTransferFailure

@[simp] theorem toContractCallFailure_senderAbsent :
    senderAbsent.toContractCallFailure = .unavailable :=
  rfl

@[simp] theorem toContractCallFailure_recipientAbsent :
    recipientAbsent.toContractCallFailure = .unavailable :=
  rfl

@[simp] theorem toContractCallFailure_insufficientBalance :
    insufficientBalance.toContractCallFailure = .insufficientBalance :=
  rfl

@[simp] theorem toContractCallFailure_recipientOverflow :
    recipientOverflow.toContractCallFailure = .balanceOverflow :=
  rfl

@[simp] theorem toContractCallResult_code (failure : BalanceTransferFailure) :
    failure.toContractCallResult =
      .failed failure.toContractCallFailure.code :=
  rfl

end Solcore.ContractRuntime.BalanceTransferFailure
