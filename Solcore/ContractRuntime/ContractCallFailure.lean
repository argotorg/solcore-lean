import Solcore.Core.HostMachine
import Solcore.Core.ContractCallWordResultProperties

/-! Internal failure reasons for dispatching one checked contract-word call. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Failures that occur before a child contract produces a terminal outcome. -/
inductive ContractCallFailure where
  | invalidAddress
  | unavailable
  | depthExceeded
  | insufficientBalance
  | balanceOverflow
  | nonceOverflow
  | addressCollision
  deriving Repr, BEq, DecidableEq

namespace ContractCallFailure

/-- Stable internal code injected into the typed call-failure response branch. -/
def code : ContractCallFailure → Core.Word
  | .invalidAddress => ⟨0, by decide⟩
  | .unavailable => ⟨1, by decide⟩
  | .depthExceeded => ⟨2, by decide⟩
  | .insufficientBalance => ⟨3, by decide⟩
  | .balanceOverflow => ⟨4, by decide⟩
  | .nonceOverflow => ⟨5, by decide⟩
  | .addressCollision => ⟨6, by decide⟩

/-- Convert a dispatch failure into the dedicated Core call-result branch. -/
def result (failure : ContractCallFailure) : Core.ContractCallWordResult :=
  .failed failure.code

end ContractCallFailure

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.ContractCallFailureProperties`
-/

/-! Exact codes and response injection for internal call-dispatch failures. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ContractCallFailure

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

@[simp] theorem code_nonceOverflow :
    nonceOverflow.code = ⟨5, by decide⟩ :=
  rfl

@[simp] theorem code_addressCollision :
    addressCollision.code = ⟨6, by decide⟩ :=
  rfl

@[simp] theorem result_value (failure : ContractCallFailure) :
    failure.result.value =
      .inRight .word
        (.inRight .word (.inRight .word (.word failure.code))) :=
  rfl

end Solcore.ContractRuntime.ContractCallFailure
