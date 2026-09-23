import Solcore.Frontend.WordLiteral
import Solcore.Core.Primitive

/-! ADR-0162 consumers: complete ASCII spellings have independent natural
meanings and strict Word bounds do not wrap. These tests do not require an
expression adapter; its integration is tested in FrontendLocalWordLiteralProperties. -/

set_option autoImplicit false

namespace Tests.FrontendWordLiteral

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "word-literals.sol"⟩, 0, 1⟩
private def literal (payload : Syntax.CoreLiteralValue) : Syntax.CoreLiteral := ⟨span, payload⟩
private def fortyTwo : Core.Word := ⟨42, by decide⟩
private def one : Core.Word := ⟨1, by decide⟩

private theorem decimalMeaning : NumericLiteralDenotes (.decimal "42") 42 :=
  .decimal (by decide)
    (.cons (.decimal (digit := 4) (by decide) (by decide))
      (.cons (.decimal (digit := 2) (by decide) (by decide)) .nil))
private theorem lowerHexMeaning : NumericLiteralDenotes (.hexadecimal "0x2a") 42 :=
  .hexadecimal rfl (by decide)
    (.cons (.decimal (digit := 2) (by decide) (by decide))
      (.cons (.hexLower (digit := 10) (by decide) (by decide) (by decide)) .nil))
private theorem upperHexMeaning : NumericLiteralDenotes (.hexadecimal "0x2A") 42 :=
  .hexadecimal rfl (by decide)
    (.cons (.decimal (digit := 2) (by decide) (by decide))
      (.cons (.hexUpper (digit := 10) (by decide) (by decide) (by decide)) .nil))

theorem decimal_and_both_hex_cases_have_the_same_independent_value :
    NumericLiteralDenotes (.decimal "42") 42 ∧
    NumericLiteralDenotes (.hexadecimal "0x2a") 42 ∧
    NumericLiteralDenotes (.hexadecimal "0x2A") 42 ∧
    interpretWordLiteral? (literal (.decimal "42")) = some fortyTwo ∧
    interpretWordLiteral? (literal (.hexadecimal "0x2a")) = some fortyTwo ∧
    interpretWordLiteral? (literal (.hexadecimal "0x2A")) = some fortyTwo ∧
    fortyTwo.val = 42 :=
  ⟨decimalMeaning, lowerHexMeaning, upperHexMeaning,
    interpretWordLiteral?_complete decimalMeaning,
    interpretWordLiteral?_complete lowerHexMeaning,
    interpretWordLiteral?_complete upperHexMeaning, rfl⟩

private def paddedDecimal (count : Nat) : Syntax.CoreLiteralValue :=
  .decimal (String.ofList (List.replicate count '0' ++ ['1']))
private def paddedHex (count : Nat) : Syntax.CoreLiteralValue :=
  .hexadecimal (String.ofList ('0' :: 'x' :: (List.replicate count '0' ++ ['1'])))
private theorem oneDigits (radix : NumericRadix) : NumericDigitsDenote radix ['1'] 0 1 := by
  simpa only [Nat.mul_zero, Nat.zero_add] using
    (NumericDigitsDenote.cons (initial := 0)
      (NumericDigitDenotes.decimal (radix := radix) (digit := 1) (by decide) (by decide)) .nil)
private theorem paddedDecimalMeaning (count : Nat) : NumericLiteralDenotes (paddedDecimal count) 1 := by
  apply NumericLiteralDenotes.decimal
  · simp
  · simpa using (oneDigits .decimal).leading_zeros count
private theorem paddedHexMeaning (count : Nat) : NumericLiteralDenotes (paddedHex count) 1 := by
  apply NumericLiteralDenotes.hexadecimal (characters := List.replicate count '0' ++ ['1'])
  · simp
  · simp
  · exact (oneDigits .hexadecimal).leading_zeros count

theorem arbitrarily_many_leading_zeroes_preserve_exact_value (count : Nat) :
    NumericLiteralDenotes (paddedDecimal count) 1 ∧
    NumericLiteralDenotes (paddedHex count) 1 ∧
    numericLiteralValue? (paddedDecimal count) = some 1 ∧
    numericLiteralValue? (paddedHex count) = some 1 ∧
    interpretWordLiteral? (literal (paddedDecimal count)) = some one ∧
    interpretWordLiteral? (literal (paddedHex count)) = some one :=
  ⟨paddedDecimalMeaning count, paddedHexMeaning count,
    numericLiteralValue?_complete (paddedDecimalMeaning count),
    numericLiteralValue?_complete (paddedHexMeaning count),
    interpretWordLiteral?_complete (paddedDecimalMeaning count),
    interpretWordLiteral?_complete (paddedHexMeaning count)⟩

private def decimalMaximum : Syntax.CoreLiteralValue :=
  .decimal "115792089237316195423570985008687907853269984665640564039457584007913129639935"
private def hexMaximum : Syntax.CoreLiteralValue :=
  .hexadecimal "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
private def decimalOverflow : Syntax.CoreLiteralValue :=
  .decimal "115792089237316195423570985008687907853269984665640564039457584007913129639936"
private def hexOverflow : Syntax.CoreLiteralValue :=
  .hexadecimal "0x10000000000000000000000000000000000000000000000000000000000000000"

theorem zero_one_and_maximum_are_accepted_without_reduction :
    interpretWordLiteral? (literal (.decimal "0")) = some Core.Word.zero ∧
    interpretWordLiteral? (literal (.hexadecimal "0x0")) = some Core.Word.zero ∧
    interpretWordLiteral? (literal (.decimal "1")) = some one ∧
    interpretWordLiteral? (literal (.hexadecimal "0x1")) = some one ∧
    interpretWordLiteral? (literal decimalMaximum) = some Core.Word.maximum ∧
    interpretWordLiteral? (literal hexMaximum) = some Core.Word.maximum ∧
    WordLiteralDenotes (literal decimalMaximum) Core.Word.maximum ∧
    WordLiteralDenotes (literal hexMaximum) Core.Word.maximum := by
  have decimal : interpretWordLiteral? (literal decimalMaximum) = some Core.Word.maximum := by decide
  have hexadecimal : interpretWordLiteral? (literal hexMaximum) = some Core.Word.maximum := by decide
  exact ⟨by decide, by decide, by decide, by decide, decimal, hexadecimal,
    interpretWordLiteral?_sound decimal, interpretWordLiteral?_sound hexadecimal⟩

theorem modulus_has_a_natural_meaning_but_no_word_meaning :
    numericLiteralValue? decimalOverflow = some Core.wordModulus ∧
    numericLiteralValue? hexOverflow = some Core.wordModulus ∧
    NumericLiteralDenotes decimalOverflow Core.wordModulus ∧
    NumericLiteralDenotes hexOverflow Core.wordModulus ∧
    interpretWordLiteral? (literal decimalOverflow) = none ∧
    interpretWordLiteral? (literal hexOverflow) = none ∧
    interpretWordLiteralModulo? (literal decimalOverflow) = some Core.Word.zero ∧
    interpretWordLiteralModulo? (literal hexOverflow) = some Core.Word.zero ∧
    (¬ ∃ word, WordLiteralDenotes (literal decimalOverflow) word) ∧
    (¬ ∃ word, WordLiteralDenotes (literal hexOverflow) word) := by
  have decimal : numericLiteralValue? decimalOverflow = some Core.wordModulus := by decide
  have hexadecimal : numericLiteralValue? hexOverflow = some Core.wordModulus := by decide
  have decimalMeaning := numericLiteralValue?_sound decimal
  have hexMeaning := numericLiteralValue?_sound hexadecimal
  have decimalRejected : interpretWordLiteral? (literal decimalOverflow) = none :=
    interpretWordLiteral?_eq_none_of_out_of_range decimalMeaning (Nat.le_refl _)
  have hexRejected : interpretWordLiteral? (literal hexOverflow) = none :=
    interpretWordLiteral?_eq_none_of_out_of_range hexMeaning (Nat.le_refl _)
  have modulusWraps :
      Core.Word.ofNatModulo Core.wordModulus = Core.Word.zero := by
    apply Fin.ext
    simp [Core.Word.ofNatModulo, Core.Word.zero]
  have decimalModulo :
      interpretWordLiteralModulo? (literal decimalOverflow) =
        some Core.Word.zero := by
    apply interpretWordLiteralModulo?_complete
    exact ⟨Core.wordModulus, decimalMeaning, modulusWraps⟩
  have hexModulo :
      interpretWordLiteralModulo? (literal hexOverflow) =
        some Core.Word.zero := by
    apply interpretWordLiteralModulo?_complete
    exact ⟨Core.wordModulus, hexMeaning, modulusWraps⟩
  refine ⟨decimal, hexadecimal, decimalMeaning, hexMeaning, decimalRejected,
    hexRejected, decimalModulo, hexModulo, ?_, ?_⟩
  · rintro ⟨word, meaning⟩
    have impossible := interpretWordLiteral?_complete meaning
    rw [decimalRejected] at impossible
    cases impossible
  · rintro ⟨word, meaning⟩
    have impossible := interpretWordLiteral?_complete meaning
    rw [hexRejected] at impossible
    cases impossible

private def malformed : List Syntax.CoreLiteralValue :=
  [.decimal "", .decimal "+", .decimal "-1", .decimal "+1", .decimal " 1", .decimal "1 ",
   .decimal "1_000", .decimal "１", .decimal "١", .decimal "1.0", .decimal "12x", .decimal "0x1",
   .hexadecimal "", .hexadecimal "0x", .hexadecimal "0X", .hexadecimal "0X1", .hexadecimal "0x+1",
   .hexadecimal "0x 1", .hexadecimal "0x1_0", .hexadecimal "0xＦ", .hexadecimal "0x1g",
   .hexadecimal "12", .hexadecimal "0x1.0", .string "123", .string "0x1"]

theorem malformed_payloads_have_no_numeric_or_word_meaning
    (payload : Syntax.CoreLiteralValue) (present : payload ∈ malformed) (location : Syntax.SourceSpan) :
    numericLiteralValue? payload = none ∧
    (¬ ∃ value, NumericLiteralDenotes payload value) ∧
    interpretWordLiteral? ⟨location, payload⟩ = none ∧
    interpretWordLiteralModulo? ⟨location, payload⟩ = none ∧
    ¬ ∃ word, WordLiteralDenotes ⟨location, payload⟩ word := by
  have allRejected : ∀ candidate ∈ malformed, numericLiteralValue? candidate = none := by decide
  have rejected := allRejected payload present
  have wordRejected : interpretWordLiteral? ⟨location, payload⟩ = none := by
    simp [interpretWordLiteral?, rejected]
  have moduloRejected :
      interpretWordLiteralModulo? ⟨location, payload⟩ = none := by
    simp [interpretWordLiteralModulo?, rejected]
  refine ⟨rejected, numericLiteralValue?_eq_none_iff.mp rejected, wordRejected,
    moduloRejected, ?_⟩
  rintro ⟨word, meaning⟩
  have impossible := interpretWordLiteral?_complete meaning
  rw [wordRejected] at impossible
  cases impossible

theorem span_changes_do_not_change_interpretation_or_independent_meaning
    (payload : Syntax.CoreLiteralValue) (location otherLocation : Syntax.SourceSpan) (word : Core.Word) :
    interpretWordLiteral? ⟨location, payload⟩ = interpretWordLiteral? ⟨otherLocation, payload⟩ ∧
    (WordLiteralDenotes ⟨location, payload⟩ word ↔ WordLiteralDenotes ⟨otherLocation, payload⟩ word) ∧
    interpretWordLiteralModulo? ⟨location, payload⟩ =
      interpretWordLiteralModulo? ⟨otherLocation, payload⟩ ∧
    (ModuloWordLiteralDenotes ⟨location, payload⟩ word ↔
      ModuloWordLiteralDenotes ⟨otherLocation, payload⟩ word) :=
  ⟨interpretWordLiteral?_span payload location otherLocation,
    wordLiteralDenotes_span payload location otherLocation word,
    interpretWordLiteralModulo?_span payload location otherLocation,
    moduloWordLiteralDenotes_span payload location otherLocation word⟩

end Tests.FrontendWordLiteral
