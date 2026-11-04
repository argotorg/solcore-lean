import Std
import Solcore.Syntax.Literal
import Solcore.Core.Primitive

/-!
# Numeric literals

Digits and the mathematical meaning of numeric literals, with no general source type. Main
declarations: `NumericLiteralDenotes`, `numericLiteralValue?`, `WordLiteralDenotes`,
`interpretWordLiteral?`.
-/

section
-- leanmerge: from Solcore.Frontend.NumericDigits
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

/-!
## Consolidated module: `Solcore.Frontend.NumericDigitsProperties`
-/

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
end

section
-- leanmerge: from Solcore.Frontend.WordLiteral
/-!
Standalone mathematical numeric meaning and an explicitly strict Word projection.
These operations do not assign a general source type or extend expression checking.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Decode a complete numeric payload, validating even manually constructed ASTs. -/
def numericLiteralValue? : Syntax.CoreLiteralValue → Option Nat
  | .decimal spelling =>
      match spelling.toList with
      | [] => none
      | first :: rest => numericDigitsValue? .decimal (first :: rest) 0
  | .hexadecimal spelling =>
      match spelling.toList with
      | '0' :: 'x' :: first :: rest =>
          numericDigitsValue? .hexadecimal (first :: rest) 0
      | _ => none
  | .string _ => none

/-- Whole numeric spelling has its natural value, independently of decoding. -/
inductive NumericLiteralDenotes : Syntax.CoreLiteralValue → Nat → Prop where
  | decimal {spelling : String} {value : Nat}
      (nonempty : spelling.toList ≠ [])
      (digits : NumericDigitsDenote .decimal spelling.toList 0 value) :
      NumericLiteralDenotes (.decimal spelling) value
  | hexadecimal {spelling : String} {characters : List Char} {value : Nat}
      (spellingEq : spelling.toList = '0' :: 'x' :: characters)
      (nonempty : characters ≠ [])
      (digits : NumericDigitsDenote .hexadecimal characters 0 value) :
      NumericLiteralDenotes (.hexadecimal spelling) value

/-- Convert a numeric literal only when its natural value fits a 256-bit Word. -/
def interpretWordLiteral? (literal : Syntax.CoreLiteral) : Option Core.Word :=
  (numericLiteralValue? literal.value).bind Core.Word.ofNat?

/-- Convert a well-formed nonnegative integer literal modulo the 256-bit Word
range.  This is the conversion primitive needed by a future `Int.fromInteger`
profile; it does not alter the existing strict Word-literal adapter. -/
def interpretWordLiteralModulo? (literal : Syntax.CoreLiteral) : Option Core.Word :=
  (numericLiteralValue? literal.value).map Core.Word.ofNatModulo

/-- Strict Word meaning retains exactly the independent natural value. -/
def WordLiteralDenotes (literal : Syntax.CoreLiteral) (word : Core.Word) : Prop :=
  NumericLiteralDenotes literal.value word.val

/-- Independent meaning of the nonnegative modulo projection. -/
def ModuloWordLiteralDenotes
    (literal : Syntax.CoreLiteral) (word : Core.Word) : Prop :=
  ∃ value, NumericLiteralDenotes literal.value value ∧
    Core.Word.ofNatModulo value = word

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.WordLiteralProperties`
-/

/-! Exact natural-number meaning and failure of the explicit strict Word projection. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem numericLiteralValue?_sound {payload : Syntax.CoreLiteralValue} {value : Nat}
    (decoded : numericLiteralValue? payload = some value) :
    NumericLiteralDenotes payload value := by
  cases payload with
  | decimal spelling =>
      simp only [numericLiteralValue?] at decoded
      split at decoded
      next => contradiction
      next first rest shape =>
        exact .decimal (by simp [shape])
          (by rw [shape]; exact numericDigitsValue?_iff.mp decoded)
  | hexadecimal spelling =>
      simp only [numericLiteralValue?] at decoded
      split at decoded
      next first rest shape =>
        exact .hexadecimal shape (by simp) (numericDigitsValue?_iff.mp decoded)
      next => contradiction
  | string spelling => simp [numericLiteralValue?] at decoded

theorem numericLiteralValue?_complete {payload : Syntax.CoreLiteralValue} {value : Nat}
    (meaning : NumericLiteralDenotes payload value) :
    numericLiteralValue? payload = some value := by
  cases meaning with
  | decimal nonempty digits =>
      rename_i spelling
      cases shape : spelling.toList with
      | nil => exact False.elim (nonempty shape)
      | cons first rest =>
          simpa [numericLiteralValue?, shape] using numericDigitsValue?_iff.mpr digits
  | hexadecimal spellingEq nonempty digits =>
      rename_i spelling characters
      cases characters with
      | nil => exact False.elim (nonempty rfl)
      | cons first rest =>
          simpa [numericLiteralValue?, spellingEq] using numericDigitsValue?_iff.mpr digits

theorem numericLiteralValue?_iff {payload : Syntax.CoreLiteralValue} {value : Nat} :
    numericLiteralValue? payload = some value ↔ NumericLiteralDenotes payload value :=
  ⟨numericLiteralValue?_sound, numericLiteralValue?_complete⟩

theorem NumericLiteralDenotes.value_unique {payload : Syntax.CoreLiteralValue}
    {left right : Nat} (leftMeaning : NumericLiteralDenotes payload left)
    (rightMeaning : NumericLiteralDenotes payload right) : left = right := by
  exact Option.some.inj
    ((numericLiteralValue?_complete leftMeaning).symm.trans
      (numericLiteralValue?_complete rightMeaning))

theorem numericLiteralValue?_eq_none_iff {payload : Syntax.CoreLiteralValue} :
    numericLiteralValue? payload = none ↔ ¬ ∃ value, NumericLiteralDenotes payload value := by
  constructor
  · intro rejected ⟨value, meaning⟩
    have accepted := numericLiteralValue?_complete meaning
    simp [rejected] at accepted
  · intro absent
    cases decoded : numericLiteralValue? payload with
    | none => rfl
    | some value => exact False.elim (absent ⟨value, numericLiteralValue?_sound decoded⟩)

private theorem wordOfNat?_eq_some_iff {value : Nat} {word : Core.Word} :
    Core.Word.ofNat? value = some word ↔ value = word.val := by
  unfold Core.Word.ofNat?
  split
  next inRange =>
    constructor
    · intro equal
      exact congrArg Fin.val (Option.some.inj equal)
    · intro equal
      exact congrArg some (Fin.ext equal)
  next outOfRange =>
    constructor
    · intro equal; contradiction
    · intro equal
      exact False.elim (outOfRange (by rw [equal]; exact word.isLt))

theorem interpretWordLiteral?_sound {literal : Syntax.CoreLiteral} {word : Core.Word}
    (decoded : interpretWordLiteral? literal = some word) : WordLiteralDenotes literal word := by
  cases natural : numericLiteralValue? literal.value with
  | none => simp [interpretWordLiteral?, natural] at decoded
  | some value =>
      have equal : value = word.val := wordOfNat?_eq_some_iff.mp
        (by simpa [interpretWordLiteral?, natural] using decoded)
      change NumericLiteralDenotes literal.value word.val
      rw [← equal]
      exact numericLiteralValue?_sound natural

theorem interpretWordLiteral?_complete {literal : Syntax.CoreLiteral} {word : Core.Word}
    (meaning : WordLiteralDenotes literal word) : interpretWordLiteral? literal = some word := by
  rw [interpretWordLiteral?, numericLiteralValue?_complete meaning]
  exact wordOfNat?_eq_some_iff.mpr rfl

theorem interpretWordLiteral?_iff {literal : Syntax.CoreLiteral} {word : Core.Word} :
    interpretWordLiteral? literal = some word ↔ WordLiteralDenotes literal word :=
  ⟨interpretWordLiteral?_sound, interpretWordLiteral?_complete⟩

theorem WordLiteralDenotes.value_unique {literal : Syntax.CoreLiteral} {left right : Core.Word}
    (leftMeaning : WordLiteralDenotes literal left)
    (rightMeaning : WordLiteralDenotes literal right) : left = right := by
  exact Fin.ext (NumericLiteralDenotes.value_unique leftMeaning rightMeaning)

theorem interpretWordLiteral?_complete_of_lt {literal : Syntax.CoreLiteral} {value : Nat}
    (meaning : NumericLiteralDenotes literal.value value) (inRange : value < Core.wordModulus) :
    interpretWordLiteral? literal = some ⟨value, inRange⟩ :=
  interpretWordLiteral?_complete meaning

theorem interpretWordLiteral?_value_and_range {literal : Syntax.CoreLiteral} {word : Core.Word}
    (decoded : interpretWordLiteral? literal = some word) :
    numericLiteralValue? literal.value = some word.val ∧ word.val < Core.wordModulus :=
  ⟨numericLiteralValue?_complete (interpretWordLiteral?_sound decoded), word.isLt⟩

theorem interpretWordLiteral?_eq_none_of_out_of_range
    {literal : Syntax.CoreLiteral} {value : Nat}
    (meaning : NumericLiteralDenotes literal.value value) (outOfRange : Core.wordModulus ≤ value) :
    interpretWordLiteral? literal = none := by
  simp [interpretWordLiteral?, numericLiteralValue?_complete meaning, Core.Word.ofNat?,
    Nat.not_lt.mpr outOfRange]

theorem interpretWordLiteral?_eq_none_iff {literal : Syntax.CoreLiteral} :
    interpretWordLiteral? literal = none ↔
      (¬ ∃ value, NumericLiteralDenotes literal.value value) ∨
        ∃ value, NumericLiteralDenotes literal.value value ∧ Core.wordModulus ≤ value := by
  constructor
  · intro rejected
    cases decoded : numericLiteralValue? literal.value with
    | none => exact Or.inl (numericLiteralValue?_eq_none_iff.mp decoded)
    | some value =>
        refine Or.inr ⟨value, numericLiteralValue?_sound decoded, ?_⟩
        apply Nat.le_of_not_gt
        intro inRange
        have accepted := interpretWordLiteral?_complete_of_lt
          (numericLiteralValue?_sound decoded) inRange
        simp [rejected] at accepted
  · intro absent
    rcases absent with noMeaning | ⟨value, meaning, outOfRange⟩
    · simp [interpretWordLiteral?, numericLiteralValue?_eq_none_iff.mpr noMeaning]
    · exact interpretWordLiteral?_eq_none_of_out_of_range meaning outOfRange

theorem interpretWordLiteral?_span (payload : Syntax.CoreLiteralValue)
    (span otherSpan : Syntax.SourceSpan) :
    interpretWordLiteral? ⟨span, payload⟩ = interpretWordLiteral? ⟨otherSpan, payload⟩ := rfl

theorem wordLiteralDenotes_span (payload : Syntax.CoreLiteralValue)
    (span otherSpan : Syntax.SourceSpan) (word : Core.Word) :
    WordLiteralDenotes ⟨span, payload⟩ word ↔ WordLiteralDenotes ⟨otherSpan, payload⟩ word := Iff.rfl

theorem interpretWordLiteralModulo?_sound
    {literal : Syntax.CoreLiteral} {word : Core.Word}
    (decoded : interpretWordLiteralModulo? literal = some word) :
    ModuloWordLiteralDenotes literal word := by
  cases natural : numericLiteralValue? literal.value with
  | none => simp [interpretWordLiteralModulo?, natural] at decoded
  | some value =>
      have equal : Core.Word.ofNatModulo value = word := by
        simpa [interpretWordLiteralModulo?, natural] using decoded
      exact ⟨value, numericLiteralValue?_sound natural, equal⟩

theorem interpretWordLiteralModulo?_complete
    {literal : Syntax.CoreLiteral} {word : Core.Word}
    (meaning : ModuloWordLiteralDenotes literal word) :
    interpretWordLiteralModulo? literal = some word := by
  rcases meaning with ⟨value, natural, equal⟩
  simp [interpretWordLiteralModulo?, numericLiteralValue?_complete natural, equal]

theorem interpretWordLiteralModulo?_iff
    {literal : Syntax.CoreLiteral} {word : Core.Word} :
    interpretWordLiteralModulo? literal = some word ↔
      ModuloWordLiteralDenotes literal word :=
  ⟨interpretWordLiteralModulo?_sound, interpretWordLiteralModulo?_complete⟩

theorem interpretWordLiteralModulo?_eq_none_iff
    {literal : Syntax.CoreLiteral} :
    interpretWordLiteralModulo? literal = none ↔
      ¬ ∃ value, NumericLiteralDenotes literal.value value := by
  simp [interpretWordLiteralModulo?, numericLiteralValue?_eq_none_iff]

theorem interpretWordLiteralModulo?_span (payload : Syntax.CoreLiteralValue)
    (span otherSpan : Syntax.SourceSpan) :
    interpretWordLiteralModulo? ⟨span, payload⟩ =
      interpretWordLiteralModulo? ⟨otherSpan, payload⟩ := rfl

theorem moduloWordLiteralDenotes_span (payload : Syntax.CoreLiteralValue)
    (span otherSpan : Syntax.SourceSpan) (word : Core.Word) :
    ModuloWordLiteralDenotes ⟨span, payload⟩ word ↔
      ModuloWordLiteralDenotes ⟨otherSpan, payload⟩ word := Iff.rfl

end Solcore.Frontend
end
