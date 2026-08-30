import Solcore.Core.HostStateSafety

/-! Exact decoding and injectivity for the typed contract-word call response. -/

set_option autoImplicit false

namespace Solcore.Core.ContractCallWordResult

/-- Recognize only the four canonical values emitted by `value`. -/
def ofValue? : Value → Option ContractCallWordResult
  | .inLeft (.sum .word (.sum .word .word)) (.word data) =>
      some (.returned data)
  | .inRight .word
      (.inLeft (.sum .word .word) (.word data)) =>
      some (.reverted data)
  | .inRight .word
      (.inRight .word (.inLeft .word (.word reason))) =>
      some (.trapped reason)
  | .inRight .word
      (.inRight .word (.inRight .word (.word reason))) =>
      some (.failed reason)
  | _ => none

@[simp] theorem ofValue?_value (result : ContractCallWordResult) :
    ofValue? result.value = some result := by
  cases result <;> rfl

/-- The four response constructors have disjoint, payload-preserving encodings. -/
theorem value_injective : Function.Injective value := by
  intro left right equality
  have decoded := congrArg ofValue? equality
  simpa using decoded

theorem value_eq_iff (left right : ContractCallWordResult) :
    left.value = right.value ↔ left = right :=
  ⟨fun equal => value_injective equal, congrArg value⟩

end Solcore.Core.ContractCallWordResult
