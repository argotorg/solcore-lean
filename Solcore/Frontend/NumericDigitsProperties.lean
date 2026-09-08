import Solcore.Frontend.NumericDigits

/-! Exact decoder correspondence with independent ASCII/Horner meanings.
All characters participate, and arbitrarily many leading zeroes preserve value.
No machine Word bound or source-literal typing premise is part of this layer. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem NumericDigitDenotes.complete {radix : NumericRadix} {character : Char} {digit : Nat}
    (denotes : NumericDigitDenotes radix character digit) :
    numericDigitValue? radix character = some digit := by
  cases denotes with
  | decimal bounded code =>
      have decimalRange : 48 ≤ character.toNat ∧ character.toNat ≤ 57 := by omega
      simp only [numericDigitValue?, if_pos decimalRange]
      congr 1
      omega
  | hexLower lower upper code =>
      have notDecimal : ¬ (48 ≤ character.toNat ∧ character.toNat ≤ 57) := by omega
      have lowerRange : 97 ≤ character.toNat ∧ character.toNat ≤ 102 := by omega
      simp only [numericDigitValue?, if_neg notDecimal, if_pos lowerRange]
      congr 1
      omega
  | hexUpper lower upper code =>
      have notDecimal : ¬ (48 ≤ character.toNat ∧ character.toNat ≤ 57) := by omega
      have notLower : ¬ (97 ≤ character.toNat ∧ character.toNat ≤ 102) := by omega
      have upperRange : 65 ≤ character.toNat ∧ character.toNat ≤ 70 := by omega
      simp only [numericDigitValue?, if_neg notDecimal, if_neg notLower, if_pos upperRange]
      congr 1
      omega

theorem numericDigitValue?_sound {radix : NumericRadix} {character : Char} {digit : Nat}
    (result : numericDigitValue? radix character = some digit) :
    NumericDigitDenotes radix character digit := by
  by_cases decimalRange : 48 ≤ character.toNat ∧ character.toNat ≤ 57
  · have same : character.toNat - 48 = digit := by
      simpa only [numericDigitValue?, if_pos decimalRange, Option.some.injEq] using result
    exact .decimal (by omega) (by omega)
  · cases radix with
    | decimal => simp only [numericDigitValue?, if_neg decimalRange, reduceCtorEq] at result
    | hexadecimal =>
        by_cases lowerRange : 97 ≤ character.toNat ∧ character.toNat ≤ 102
        · have same : character.toNat - 87 = digit := by
            simpa only [numericDigitValue?, if_neg decimalRange, if_pos lowerRange,
              Option.some.injEq] using result
          exact .hexLower (by omega) (by omega) (by omega)
        · by_cases upperRange : 65 ≤ character.toNat ∧ character.toNat ≤ 70
          · have same : character.toNat - 55 = digit := by
              simpa only [numericDigitValue?, if_neg decimalRange, if_neg lowerRange,
                if_pos upperRange, Option.some.injEq] using result
            exact .hexUpper (by omega) (by omega) (by omega)
          · simp only [numericDigitValue?, if_neg decimalRange, if_neg lowerRange,
              if_neg upperRange, reduceCtorEq] at result

theorem numericDigitValue?_iff {radix : NumericRadix} {character : Char} {digit : Nat} :
    numericDigitValue? radix character = some digit ↔ NumericDigitDenotes radix character digit :=
  ⟨numericDigitValue?_sound, NumericDigitDenotes.complete⟩

theorem NumericDigitDenotes.value_unique {radix : NumericRadix} {character : Char}
    {left right : Nat} (leftDenotes : NumericDigitDenotes radix character left)
    (rightDenotes : NumericDigitDenotes radix character right) : left = right :=
  Option.some.inj (leftDenotes.complete.symm.trans rightDenotes.complete)

theorem NumericDigitDenotes.lt_base {radix : NumericRadix} {character : Char} {digit : Nat}
    (denotes : NumericDigitDenotes radix character digit) : digit < radix.base := by
  cases denotes with
  | decimal bounded _ => cases radix <;> simp only [NumericRadix.base] <;> omega
  | hexLower _ upper _ | hexUpper _ upper _ => exact upper

theorem numericDigitValue?_eq_none_iff {radix : NumericRadix} {character : Char} :
    numericDigitValue? radix character = none ↔ ¬ ∃ digit, NumericDigitDenotes radix character digit := by
  constructor
  · intro absent ⟨digit, denotes⟩
    have impossible := denotes.complete
    rw [absent] at impossible
    cases impossible
  · intro absent
    cases result : numericDigitValue? radix character with
    | none => rfl
    | some digit => exact False.elim (absent ⟨digit, numericDigitValue?_sound result⟩)

theorem NumericDigitsDenote.complete {radix : NumericRadix} {characters : List Char}
    {initial final : Nat} (denotes : NumericDigitsDenote radix characters initial final) :
    numericDigitsValue? radix characters initial = some final := by
  induction denotes with
  | nil => rfl
  | cons head _ ih => simpa only [numericDigitsValue?, head.complete, bind, Option.bind_some] using ih

theorem numericDigitsValue?_sound {radix : NumericRadix} {characters : List Char}
    {initial final : Nat} (result : numericDigitsValue? radix characters initial = some final) :
    NumericDigitsDenote radix characters initial final := by
  induction characters generalizing initial with
  | nil =>
      simp only [numericDigitsValue?, Option.some.injEq] at result
      cases result
      exact .nil
  | cons character rest ih =>
      simp only [numericDigitsValue?, bind, Option.bind_eq_some_iff] at result
      obtain ⟨digit, headResult, tailResult⟩ := result
      exact .cons (numericDigitValue?_sound headResult) (ih tailResult)

theorem numericDigitsValue?_iff {radix : NumericRadix} {characters : List Char} {initial final : Nat} :
    numericDigitsValue? radix characters initial = some final ↔
      NumericDigitsDenote radix characters initial final :=
  ⟨numericDigitsValue?_sound, NumericDigitsDenote.complete⟩

theorem NumericDigitsDenote.value_unique {radix : NumericRadix} {characters : List Char}
    {initial left right : Nat} (leftDenotes : NumericDigitsDenote radix characters initial left)
    (rightDenotes : NumericDigitsDenote radix characters initial right) : left = right :=
  Option.some.inj (leftDenotes.complete.symm.trans rightDenotes.complete)

theorem numericDigitsValue?_eq_none_iff {radix : NumericRadix} {characters : List Char} {initial : Nat} :
    numericDigitsValue? radix characters initial = none ↔
      ¬ ∃ final, NumericDigitsDenote radix characters initial final := by
  constructor
  · intro absent ⟨final, denotes⟩
    have impossible := denotes.complete
    rw [absent] at impossible
    cases impossible
  · intro absent
    cases result : numericDigitsValue? radix characters initial with
    | none => rfl
    | some final => exact False.elim (absent ⟨final, numericDigitsValue?_sound result⟩)

theorem numericDigitsValue?_leading_zero (radix : NumericRadix) (characters : List Char) :
    numericDigitsValue? radix ('0' :: characters) 0 = numericDigitsValue? radix characters 0 := by
  have zero : numericDigitValue? radix '0' = some 0 :=
    (NumericDigitDenotes.decimal (by decide) (by decide)).complete
  simp only [numericDigitsValue?, zero, bind, Option.bind_some, Nat.mul_zero, Nat.zero_add]

/-- Any finite number of leading zeroes preserves an independently denoted value. -/
theorem NumericDigitsDenote.leading_zeros {radix : NumericRadix} {characters : List Char} {final : Nat}
    (denotes : NumericDigitsDenote radix characters 0 final) (count : Nat) :
    NumericDigitsDenote radix (List.replicate count '0' ++ characters) 0 final := by
  induction count with
  | zero => simpa using denotes
  | succ count ih =>
      have zero : NumericDigitDenotes radix '0' 0 := .decimal (by decide) (by decide)
      simpa only [List.replicate_succ, List.cons_append, Nat.mul_zero, Nat.zero_add] using
        (NumericDigitsDenote.cons zero ih)

end Solcore.Frontend
