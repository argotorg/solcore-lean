import Solcore.Core.Wire.Codec.Type

/-! Canonicalization laws which do not conflate budgets with protocol errors. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

theorem canonicalizeTypeWithBudget_of_decode_eq_ok
    (limits : CoreBudgetLimits)
    (json : Lean.Json)
    (type : Ty)
    (success : decodeTypeWithBudget limits json = .ok type) :
    canonicalizeTypeWithBudget limits json = .ok (encodeType type) := by
  rw [canonicalizeTypeWithBudget, success]
  rfl

end Solcore.Core.Wire
