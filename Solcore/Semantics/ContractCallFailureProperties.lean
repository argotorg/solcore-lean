import Solcore.Core.ContractCallWordResultProperties
import Solcore.Semantics.ContractCallFailure

/-! Exact codes and response injection for internal call-dispatch failures. -/

set_option autoImplicit false

namespace Solcore.Semantics.ContractCallFailure

theorem code_injective : Function.Injective code := by
  intro left right equal
  cases left <;> cases right <;> simp_all [code]

theorem code_eq_iff (left right : ContractCallFailure) :
    left.code = right.code ↔ left = right :=
  ⟨fun equal => code_injective equal, congrArg code⟩

theorem result_injective : Function.Injective result := by
  intro left right equal
  cases left <;> cases right <;> simp_all [result, code]

@[simp] theorem code_insufficientBalance :
    insufficientBalance.code = ⟨3, by decide⟩ :=
  rfl

@[simp] theorem code_balanceOverflow :
    balanceOverflow.code = ⟨4, by decide⟩ :=
  rfl

@[simp] theorem result_value (failure : ContractCallFailure) :
    failure.result.value =
      .inRight .word
        (.inRight .word (.inRight .word (.word failure.code))) :=
  rfl

end Solcore.Semantics.ContractCallFailure
