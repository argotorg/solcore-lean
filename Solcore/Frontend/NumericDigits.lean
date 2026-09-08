import Std

/-! Standalone ASCII numeric digits and unbounded natural-number accumulation.
This layer accepts an empty sequence with its initial accumulator; literal
wrappers must separately require at least one digit and validate any prefix.
No source literal type, Word reduction, or local-expression support is implied. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive NumericRadix where
  | decimal
  | hexadecimal
  deriving Repr, DecidableEq

def NumericRadix.base : NumericRadix → Nat
  | .decimal => 10
  | .hexadecimal => 16

/-- Exact ASCII decoding: no Unicode digits, separators, or ignored characters. -/
def numericDigitValue? (radix : NumericRadix) (character : Char) : Option Nat :=
  let code := character.toNat
  if 48 ≤ code ∧ code ≤ 57 then some (code - 48)
  else match radix with
    | .decimal => none
    | .hexadecimal =>
        if 97 ≤ code ∧ code ≤ 102 then some (code - 87)
        else if 65 ≤ code ∧ code ≤ 70 then some (code - 55)
        else none

/-- Independent ASCII positional values. Letter constructors exist only for
hexadecimal; decimal-shaped digits are shared by the two radices. -/
inductive NumericDigitDenotes : NumericRadix → Char → Nat → Prop where
  | decimal {radix : NumericRadix} {character : Char} {digit : Nat}
      (bounded : digit < 10) (code : character.toNat = 48 + digit) :
      NumericDigitDenotes radix character digit
  | hexLower {character : Char} {digit : Nat}
      (lower : 10 ≤ digit) (upper : digit < 16) (code : character.toNat = 87 + digit) :
      NumericDigitDenotes .hexadecimal character digit
  | hexUpper {character : Char} {digit : Nat}
      (lower : 10 ≤ digit) (upper : digit < 16) (code : character.toNat = 55 + digit) :
      NumericDigitDenotes .hexadecimal character digit

/-- Tail-recursive Horner accumulation in Nat, without a spelling-length bound. -/
def numericDigitsValue? (radix : NumericRadix) : List Char → Nat → Option Nat
  | [], initial => some initial
  | character :: rest, initial => do
      let digit ← numericDigitValue? radix character
      numericDigitsValue? radix rest (radix.base * initial + digit)

/-- Independent positional accumulation, including the caller's initial value. -/
inductive NumericDigitsDenote (radix : NumericRadix) : List Char → Nat → Nat → Prop where
  | nil {initial : Nat} : NumericDigitsDenote radix [] initial initial
  | cons {character : Char} {rest : List Char} {initial digit final : Nat}
      (head : NumericDigitDenotes radix character digit)
      (tail : NumericDigitsDenote radix rest (radix.base * initial + digit) final) :
      NumericDigitsDenote radix (character :: rest) initial final

end Solcore.Frontend
