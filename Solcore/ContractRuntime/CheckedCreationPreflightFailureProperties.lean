import Solcore.ContractRuntime.CheckedCreationPreflightFailure
import Solcore.ContractRuntime.ContractCallFailureProperties

/-! Exact stable codes for checked creation preflight failure injection. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedCreationPreflightFailure

@[simp] theorem unavailable_code :
    CheckedCreationPreflightFailure.unavailable.toContractCallFailure.code =
      ⟨1, by decide⟩ := by
  rfl

@[simp] theorem nonceOverflow_code :
    CheckedCreationPreflightFailure.nonceOverflow.toContractCallFailure.code =
      ⟨5, by decide⟩ := by
  rfl

@[simp] theorem addressCollision_code :
    CheckedCreationPreflightFailure.addressCollision.toContractCallFailure.code =
      ⟨6, by decide⟩ := by
  rfl

@[simp] theorem transfer_code (failure : BalanceTransferFailure) :
    (CheckedCreationPreflightFailure.transfer failure).toContractCallFailure =
      failure.toContractCallFailure := by
  rfl

@[simp] theorem result_value (failure : CheckedCreationPreflightFailure) :
    failure.toContractCallResult.value =
      .inRight .word
        (.inRight .word
          (.inRight .word
            (.word failure.toContractCallFailure.code))) := by
  cases failure <;> rfl

@[simp] theorem result_response (failure : CheckedCreationPreflightFailure) :
    Core.HostRequest.responseValue
        (.createContractWord Core.Word.zero Core.Word.zero Core.Word.zero)
        failure.toContractCallResult =
      failure.toContractCallResult.value := by
  rfl

end Solcore.ContractRuntime.CheckedCreationPreflightFailure
