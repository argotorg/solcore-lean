import Lean.Data.Json

set_option autoImplicit false

namespace Solcore.Util

private def dividePowerOfTen? : Nat → Nat → Option Nat
  | 0, value => some value
  | exponent + 1, value =>
      if value % 10 == 0 then
        dividePowerOfTen? exponent (value / 10)
      else
        none

/--
Returns the represented natural number, accepting every JSON number whose
mathematical value is a non-negative integer. Decimal and exponent spellings
therefore have the same meaning as their canonical integer spelling.
-/
def jsonNatural? : Lean.Json → Option Nat
  | .num number =>
      if number.mantissa < 0 then
        none
      else
        let value := number.mantissa.natAbs
        if value == 0 then
          some 0
        else
          dividePowerOfTen? number.exponent value
  | _ => none

@[simp] theorem jsonNatural_toJson (value : Nat) :
    jsonNatural? (Lean.toJson value) = some value := by
  change jsonNatural? (.num (Lean.JsonNumber.fromNat value)) = some value
  by_cases isZero : value = 0
  · subst value
    rfl
  · simp [jsonNatural?, Lean.JsonNumber.fromNat, dividePowerOfTen?, isZero]

end Solcore.Util
