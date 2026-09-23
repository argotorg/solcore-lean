import Solcore.Frontend.NumericDigits
import Solcore.Syntax.Literal
import Solcore.Core.Primitive

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
