import Solcore.Surface.Token

set_option autoImplicit false

namespace Solcore.Surface

inductive LexErrorKind where
  | invalidCharacter (character : Char)
  | unterminatedBlockComment
  deriving Repr, BEq, DecidableEq

structure LexError where
  code : String
  span : SourceSpan
  kind : LexErrorKind
  deriving Repr, BEq, DecidableEq

/-!
The declarative lexical grammar for successful M2a lexing.

`Lexed.ValidFor` establishes exact source slices, canonical token payloads,
well-formed line and nested block comments, source-ordering, disjointness, and
complete coverage modulo ASCII whitespace. This module adds the independent
maximal-munch obligations that are intentionally absent from that structural
validity predicate.
-/
namespace LexicalGrammar

private def byteAt (file : SourceFile) (offset : Nat) : Option UInt8 :=
  file.content.toByteArray.data[offset]?

private def isAsciiLowerByte (byte : UInt8) : Bool :=
  97 ≤ byte && byte ≤ 122

private def isAsciiUpperByte (byte : UInt8) : Bool :=
  65 ≤ byte && byte ≤ 90

private def isAsciiDigitByte (byte : UInt8) : Bool :=
  48 ≤ byte && byte ≤ 57

private def isAsciiHexDigitByte (byte : UInt8) : Bool :=
  isAsciiDigitByte byte ||
    (97 ≤ byte && byte ≤ 102) ||
    (65 ≤ byte && byte ≤ 70)

private def isIdentifierContinueByte (byte : UInt8) : Bool :=
  isAsciiLowerByte byte ||
    isAsciiUpperByte byte ||
    isAsciiDigitByte byte ||
    byte == 95

/-- Raw executable equation for source-byte lookup. -/
theorem byteAt_equation (file : SourceFile) (offset : Nat) :
    byteAt file offset = file.content.toByteArray.data[offset]? := by
  rfl

/-- Raw executable equation for ASCII decimal-digit bytes. -/
theorem isAsciiDigitByte_equation (byte : UInt8) :
    isAsciiDigitByte byte = (48 ≤ byte && byte ≤ 57) := by
  rfl

/-- Raw executable equation for ASCII hexadecimal-digit bytes. -/
theorem isAsciiHexDigitByte_equation (byte : UInt8) :
    isAsciiHexDigitByte byte =
      ((48 ≤ byte && byte ≤ 57) ||
        (97 ≤ byte && byte ≤ 102) ||
        (65 ≤ byte && byte ≤ 70)) := by
  rfl

/-- Raw executable equation for ASCII identifier-continuation bytes. -/
theorem isIdentifierContinueByte_equation (byte : UInt8) :
    isIdentifierContinueByte byte =
      ((97 ≤ byte && byte ≤ 122) ||
        (65 ≤ byte && byte ≤ 90) ||
        (48 ≤ byte && byte ≤ 57) ||
        byte == 95) := by
  rfl

/-- A source byte at `offset` can continue an ASCII identifier. -/
def IdentifierContinuesAt (file : SourceFile) (offset : Nat) : Prop :=
  ∃ byte, byteAt file offset = some byte ∧ isIdentifierContinueByte byte = true

/-- A source byte at `offset` can continue a decimal literal. -/
def DecimalContinuesAt (file : SourceFile) (offset : Nat) : Prop :=
  ∃ byte, byteAt file offset = some byte ∧ isAsciiDigitByte byte = true

/-- A source byte at `offset` can continue a hexadecimal literal. -/
def HexadecimalContinuesAt (file : SourceFile) (offset : Nat) : Prop :=
  ∃ byte, byteAt file offset = some byte ∧ isAsciiHexDigitByte byte = true

/--
An eligible hexadecimal literal starts at `offset`. The closed lexer gives
this form priority over the decimal token `0`.
-/
def EligibleHexadecimalAt (file : SourceFile) (offset : Nat) : Prop :=
  byteAt file offset = some 48 ∧
    byteAt file (offset + 1) = some 120 ∧
    HexadecimalContinuesAt file (offset + 2)

private def identifierContinuesAt (file : SourceFile) (offset : Nat) : Bool :=
  match byteAt file offset with
  | some byte => isIdentifierContinueByte byte
  | none => false

private def decimalContinuesAt (file : SourceFile) (offset : Nat) : Bool :=
  match byteAt file offset with
  | some byte => isAsciiDigitByte byte
  | none => false

private def hexadecimalContinuesAt (file : SourceFile) (offset : Nat) : Bool :=
  match byteAt file offset with
  | some byte => isAsciiHexDigitByte byte
  | none => false

private def eligibleHexadecimalAt (file : SourceFile) (offset : Nat) : Bool :=
  byteAt file offset == some 48 &&
    byteAt file (offset + 1) == some 120 &&
    hexadecimalContinuesAt file (offset + 2)

theorem identifierContinuesAt_eq_true_iff
    (file : SourceFile)
    (offset : Nat) :
    identifierContinuesAt file offset = true ↔
      IdentifierContinuesAt file offset := by
  simp [identifierContinuesAt, IdentifierContinuesAt]
  split <;> simp_all

theorem decimalContinuesAt_eq_true_iff
    (file : SourceFile)
    (offset : Nat) :
    decimalContinuesAt file offset = true ↔
      DecimalContinuesAt file offset := by
  simp [decimalContinuesAt, DecimalContinuesAt]
  split <;> simp_all

theorem hexadecimalContinuesAt_eq_true_iff
    (file : SourceFile)
    (offset : Nat) :
    hexadecimalContinuesAt file offset = true ↔
      HexadecimalContinuesAt file offset := by
  simp [hexadecimalContinuesAt, HexadecimalContinuesAt]
  split <;> simp_all

theorem eligibleHexadecimalAt_eq_true_iff
    (file : SourceFile)
    (offset : Nat) :
    eligibleHexadecimalAt file offset = true ↔
      EligibleHexadecimalAt file offset := by
  simp [eligibleHexadecimalAt, EligibleHexadecimalAt,
    hexadecimalContinuesAt_eq_true_iff, and_assoc]

private theorem bool_eq_false_iff_not_eq_true (value : Bool) :
    value = false ↔ ¬ value = true := by
  cases value <;> simp

private theorem not_or_iff_imp (proposition conclusion : Prop) :
    (¬ proposition ∨ conclusion) ↔ (proposition → conclusion) := by
  by_cases holds : proposition <;> simp [holds]

theorem identifierContinuesAt_eq_false_iff
    (file : SourceFile)
    (offset : Nat) :
    identifierContinuesAt file offset = false ↔
      ¬ IdentifierContinuesAt file offset :=
  (bool_eq_false_iff_not_eq_true _).trans
    (not_congr (identifierContinuesAt_eq_true_iff file offset))

theorem decimalContinuesAt_eq_false_iff
    (file : SourceFile)
    (offset : Nat) :
    decimalContinuesAt file offset = false ↔
      ¬ DecimalContinuesAt file offset :=
  (bool_eq_false_iff_not_eq_true _).trans
    (not_congr (decimalContinuesAt_eq_true_iff file offset))

theorem hexadecimalContinuesAt_eq_false_iff
    (file : SourceFile)
    (offset : Nat) :
    hexadecimalContinuesAt file offset = false ↔
      ¬ HexadecimalContinuesAt file offset :=
  (bool_eq_false_iff_not_eq_true _).trans
    (not_congr (hexadecimalContinuesAt_eq_true_iff file offset))

theorem eligibleHexadecimalAt_eq_false_iff
    (file : SourceFile)
    (offset : Nat) :
    eligibleHexadecimalAt file offset = false ↔
      ¬ EligibleHexadecimalAt file offset :=
  (bool_eq_false_iff_not_eq_true _).trans
    (not_congr (eligibleHexadecimalAt_eq_true_iff file offset))

/--
The local maximal-munch obligation for a token.

Identifier-shaped tokens include hard keywords, so `functionName` cannot be
split into `function` followed by `Name`. Decimal and hexadecimal runs stop
only when their respective digit classes stop. An eligible `0x` prefix has
priority over decimal `0`. The single-character forms of the five overlapping
punctuation families may be used only when their longer form is unavailable.
In particular, `/` cannot consume either comment opener.
-/
def TokenMaximalFor (token : Token) (file : SourceFile) : Prop :=
  let next := token.span.endByte
  match token.kind with
  | .keywordFunction
  | .keywordLet
  | .keywordIf
  | .keywordElse
  | .keywordReturn
  | .identifier _ =>
      ¬ IdentifierContinuesAt file next
  | .decimal digits =>
      ¬ DecimalContinuesAt file next ∧
        (digits = "0" → ¬ EligibleHexadecimalAt file token.span.startByte)
  | .hexadecimal _ =>
      ¬ HexadecimalContinuesAt file next
  | .minus =>
      byteAt file next ≠ some 62
  | .equal =>
      byteAt file next ≠ some 61
  | .bang =>
      byteAt file next ≠ some 61
  | .less =>
      byteAt file next ≠ some 61
  | .greater =>
      byteAt file next ≠ some 61
  | .slash =>
      byteAt file next ≠ some 47 ∧ byteAt file next ≠ some 42
  | _ =>
      True

/-- Executable decision procedure for `TokenMaximalFor`. -/
def tokenIsMaximalFor (token : Token) (file : SourceFile) : Bool :=
  let next := token.span.endByte
  match token.kind with
  | .keywordFunction
  | .keywordLet
  | .keywordIf
  | .keywordElse
  | .keywordReturn
  | .identifier _ =>
      !identifierContinuesAt file next
  | .decimal digits =>
      !decimalContinuesAt file next &&
        (digits != "0" || !eligibleHexadecimalAt file token.span.startByte)
  | .hexadecimal _ =>
      !hexadecimalContinuesAt file next
  | .minus =>
      byteAt file next != some 62
  | .equal =>
      byteAt file next != some 61
  | .bang =>
      byteAt file next != some 61
  | .less =>
      byteAt file next != some 61
  | .greater =>
      byteAt file next != some 61
  | .slash =>
      byteAt file next != some 47 && byteAt file next != some 42
  | _ =>
      true

theorem tokenIsMaximalFor_eq_true_iff
    (token : Token)
    (file : SourceFile) :
    tokenIsMaximalFor token file = true ↔ TokenMaximalFor token file := by
  cases token with
  | mk kind span =>
      cases kind <;>
        simp [tokenIsMaximalFor, TokenMaximalFor,
          identifierContinuesAt_eq_false_iff,
          decimalContinuesAt_eq_false_iff,
          hexadecimalContinuesAt_eq_false_iff,
          eligibleHexadecimalAt_eq_false_iff, not_or_iff_imp]

private theorem tokenSpanLength_eq_textLength
    (token : Token)
    (file : SourceFile)
    (valid : token.ValidFor file) :
    token.span.endByte - token.span.startByte =
      token.kind.text.toList.length := by
  have sizes := congrArg ByteArray.size valid.2.2
  have endInBounds :
      token.span.endByte ≤ file.content.toByteArray.size := by
    simpa using valid.2.1.2
  rw [ByteArray.size_extract, Nat.min_eq_left endInBounds,
    String.size_toByteArray] at sizes
  change token.span.endByte - token.span.startByte =
    token.kind.text.utf8ByteSize at sizes
  rw [TokenKind.canonical_text_utf8ByteSize_eq_length
    token.kind valid.1] at sizes
  exact sizes

private theorem tokenTextBytePrefix_of_start_eq_of_end_le
    (first second : Token)
    (file : SourceFile)
    (firstValid : first.ValidFor file)
    (secondValid : second.ValidFor file)
    (startEquation : first.span.startByte = second.span.startByte)
    (endLe : first.span.endByte ≤ second.span.endByte) :
    first.kind.text.toByteArray.data.toList <+:
      second.kind.text.toByteArray.data.toList := by
  change first.text.toByteArray.data.toList <+:
    second.text.toByteArray.data.toList
  rw [← firstValid.2.2, ← secondValid.2.2, startEquation]
  simp only [ByteArray.data_extract, Array.toList_extract]
  exact List.take_prefix_take_left
    (l := List.drop second.span.startByte
      file.content.toByteArray.data.toList)
    (Nat.sub_le_sub_right endLe second.span.startByte)

private theorem tokenTextCharPrefix_of_start_eq_of_end_le
    (first second : Token)
    (file : SourceFile)
    (firstValid : first.ValidFor file)
    (secondValid : second.ValidFor file)
    (startEquation : first.span.startByte = second.span.startByte)
    (endLe : first.span.endByte ≤ second.span.endByte) :
    first.kind.text.toList <+: second.kind.text.toList :=
  TokenKind.text_toList_prefix_of_canonical_of_byte_prefix
    first.kind second.kind firstValid.1 secondValid.1
    (tokenTextBytePrefix_of_start_eq_of_end_le
      first second file firstValid secondValid startEquation endLe)

private theorem tokenText_getElem?_eq_byteAt
    (token : Token)
    (file : SourceFile)
    (valid : token.ValidFor file)
    (index : Nat)
    (startLe : token.span.startByte ≤ index)
    (indexLt : index < token.span.endByte) :
    (token.kind.text.toByteArray.data.toList)[index - token.span.startByte]? =
      byteAt file index := by
  unfold byteAt
  rw [← Array.getElem?_toList]
  change token.text.toByteArray.data.toList[index - token.span.startByte]? = _
  rw [← valid.2.2]
  simp only [ByteArray.data_extract, Array.toList_extract]
  rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop]
  congr 1
  omega

private theorem byteAt_eq_nextChar_of_strict_textPrefix
    (first second : Token)
    (file : SourceFile)
    (firstValid : first.ValidFor file)
    (secondValid : second.ValidFor file)
    (startEquation : first.span.startByte = second.span.startByte)
    (next : Char)
    (suffix : List Char)
    (textEquation :
      first.kind.text.toList ++ next :: suffix =
        second.kind.text.toList) :
    byteAt file first.span.endByte =
      some (UInt8.ofNat next.toNat) := by
  have firstLength := tokenSpanLength_eq_textLength first file firstValid
  have secondLength := tokenSpanLength_eq_textLength second file secondValid
  have characterLengths := congrArg List.length textEquation
  simp only [List.length_append, List.length_cons] at characterLengths
  have firstOrdered := firstValid.2.1.1.2
  have secondOrdered := secondValid.2.1.1.2
  have firstEndLtSecondEnd :
      first.span.endByte < second.span.endByte := by
    rw [startEquation] at firstLength
    omega
  have lookup := tokenText_getElem?_eq_byteAt second file secondValid
    first.span.endByte (by omega) firstEndLtSecondEnd
  rw [TokenKind.canonical_text_bytes second.kind secondValid.1] at lookup
  rw [← textEquation] at lookup
  have relativeOffset :
      first.span.endByte - second.span.startByte =
        first.kind.text.toList.length := by
    rw [← startEquation]
    exact firstLength
  rw [relativeOffset] at lookup
  simp at lookup
  exact lookup.symm

private theorem charToNat_le_of_le
    (character upper : Char)
    (le : character ≤ upper) :
    character.toNat ≤ upper.toNat := by
  change character.val ≤ upper.val at le
  change character.val.toBitVec ≤ upper.val.toBitVec at le
  exact BitVec.le_def.mp le

private theorem charToNat_ge_of_ge
    (character lower : Char)
    (le : lower ≤ character) :
    lower.toNat ≤ character.toNat :=
  charToNat_le_of_le lower character le

private theorem uint8OfNat_le_of_le
    (first second : Nat)
    (firstLt : first < 256)
    (secondLt : second < 256)
    (le : first ≤ second) :
    UInt8.ofNat first ≤ UInt8.ofNat second := by
  change (UInt8.ofNat first).toBitVec ≤
    (UInt8.ofNat second).toBitVec
  rw [BitVec.le_def]
  simpa [Nat.mod_eq_of_lt firstLt, Nat.mod_eq_of_lt secondLt] using le

private theorem identifierContinueByte_of_character
    (character : Char)
    (continuation :
      TokenKind.IdentifierContinueCharacter character) :
    isIdentifierContinueByte (UInt8.ofNat character.toNat) = true := by
  simp [TokenKind.IdentifierContinueCharacter] at continuation
  rcases continuation with lower | upper | digit | underscore
  · have lowerNat : 97 ≤ character.toNat := by
      simpa using charToNat_ge_of_ge character 'a' lower.1
    have upperNat : character.toNat ≤ 122 := by
      simpa using charToNat_le_of_le character 'z' lower.2
    have lowerByte :
        isAsciiLowerByte (UInt8.ofNat character.toNat) = true := by
      simp only [isAsciiLowerByte, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨uint8OfNat_le_of_le 97 character.toNat (by decide)
          (by omega) lowerNat,
        uint8OfNat_le_of_le character.toNat 122 (by omega)
          (by decide) upperNat⟩
    simp [isIdentifierContinueByte, lowerByte]
  · have lowerNat : 65 ≤ character.toNat := by
      simpa using charToNat_ge_of_ge character 'A' upper.1
    have upperNat : character.toNat ≤ 90 := by
      simpa using charToNat_le_of_le character 'Z' upper.2
    have upperByte :
        isAsciiUpperByte (UInt8.ofNat character.toNat) = true := by
      simp only [isAsciiUpperByte, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨uint8OfNat_le_of_le 65 character.toNat (by decide)
          (by omega) lowerNat,
        uint8OfNat_le_of_le character.toNat 90 (by omega)
          (by decide) upperNat⟩
    simp [isIdentifierContinueByte, upperByte]
  · have lowerNat : 48 ≤ character.toNat := by
      simpa using charToNat_ge_of_ge character '0' digit.1
    have upperNat : character.toNat ≤ 57 := by
      simpa using charToNat_le_of_le character '9' digit.2
    have digitByte :
        isAsciiDigitByte (UInt8.ofNat character.toNat) = true := by
      simp only [isAsciiDigitByte, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨uint8OfNat_le_of_le 48 character.toNat (by decide)
          (by omega) lowerNat,
        uint8OfNat_le_of_le character.toNat 57 (by omega)
          (by decide) upperNat⟩
    simp [isIdentifierContinueByte, digitByte]
  · subst character
    decide

private theorem decimalContinueByte_of_character
    (character : Char)
    (continuation : TokenKind.DecimalContinueCharacter character) :
    isAsciiDigitByte (UInt8.ofNat character.toNat) = true := by
  simp [TokenKind.DecimalContinueCharacter] at continuation
  have lowerNat : 48 ≤ character.toNat := by
    simpa using charToNat_ge_of_ge character '0' continuation.1
  have upperNat : character.toNat ≤ 57 := by
    simpa using charToNat_le_of_le character '9' continuation.2
  simp only [isAsciiDigitByte, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨uint8OfNat_le_of_le 48 character.toNat (by decide)
      (by omega) lowerNat,
    uint8OfNat_le_of_le character.toNat 57 (by omega)
      (by decide) upperNat⟩

private theorem hexadecimalContinueByte_of_character
    (character : Char)
    (continuation :
      TokenKind.HexadecimalContinueCharacter character) :
    isAsciiHexDigitByte (UInt8.ofNat character.toNat) = true := by
  rcases continuation with decimal | lower | upper
  · simp [isAsciiHexDigitByte,
      decimalContinueByte_of_character character decimal]
  · have lowerNat : 97 ≤ character.toNat := by
      simpa using charToNat_ge_of_ge character 'a' lower.1
    have upperNat : character.toNat ≤ 102 := by
      simpa using charToNat_le_of_le character 'f' lower.2
    have lowerHexByte :
        (97 ≤ UInt8.ofNat character.toNat &&
          UInt8.ofNat character.toNat ≤ 102) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨uint8OfNat_le_of_le 97 character.toNat (by decide)
          (by omega) lowerNat,
        uint8OfNat_le_of_le character.toNat 102 (by omega)
          (by decide) upperNat⟩
    simp [isAsciiHexDigitByte, lowerHexByte]
  · have lowerNat : 65 ≤ character.toNat := by
      simpa using charToNat_ge_of_ge character 'A' upper.1
    have upperNat : character.toNat ≤ 70 := by
      simpa using charToNat_le_of_le character 'F' upper.2
    have upperHexByte :
        (65 ≤ UInt8.ofNat character.toNat &&
          UInt8.ofNat character.toNat ≤ 70) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨uint8OfNat_le_of_le 65 character.toNat (by decide)
          (by omega) lowerNat,
        uint8OfNat_le_of_le character.toNat 70 (by omega)
          (by decide) upperNat⟩
    simp [isAsciiHexDigitByte, upperHexByte]

private theorem eligibleHexadecimalAt_of_validFor
    (token : Token)
    (file : SourceFile)
    (digits : String)
    (valid : token.ValidFor file)
    (kindEquation : token.kind = .hexadecimal digits) :
    EligibleHexadecimalAt file token.span.startByte := by
  have digitsCanonical : (TokenKind.hexadecimal digits).Canonical := by
    rw [← kindEquation]
    exact valid.1
  rcases TokenKind.canonical_hexadecimal_digits digits digitsCanonical with
    ⟨firstDigit, remainingDigits, digitsCharacters, allDigits⟩
  have lengthEquation := tokenSpanLength_eq_textLength token file valid
  rw [kindEquation] at lengthEquation
  simp only [TokenKind.text, String.toList_append] at lengthEquation
  rw [digitsCharacters] at lengthEquation
  simp at lengthEquation
  have ordered := valid.2.1.1.2
  have startByte := tokenText_getElem?_eq_byteAt token file valid
    token.span.startByte (by omega) (by omega)
  have secondByte := tokenText_getElem?_eq_byteAt token file valid
    (token.span.startByte + 1) (by omega) (by omega)
  have thirdByte := tokenText_getElem?_eq_byteAt token file valid
    (token.span.startByte + 2) (by omega) (by omega)
  rw [TokenKind.canonical_text_bytes token.kind valid.1] at startByte secondByte thirdByte
  simp [kindEquation, TokenKind.text, String.toList_append,
    digitsCharacters] at startByte secondByte thirdByte
  refine ⟨startByte.symm, secondByte.symm, ?_⟩
  refine ⟨UInt8.ofNat firstDigit.toNat, thirdByte.symm, ?_⟩
  exact hexadecimalContinueByte_of_character firstDigit
    (allDigits firstDigit (by simp [digitsCharacters]))

private theorem strictTokenPrefix_contradicts_maximality
    (first second : Token)
    (file : SourceFile)
    (firstValid : first.ValidFor file)
    (secondValid : second.ValidFor file)
    (startEquation : first.span.startByte = second.span.startByte)
    (next : Char)
    (suffix : List Char)
    (textEquation :
      first.kind.text.toList ++ next :: suffix =
        second.kind.text.toList)
    (firstMaximal : TokenMaximalFor first file) :
    False := by
  have nextByte := byteAt_eq_nextChar_of_strict_textPrefix
    first second file firstValid secondValid startEquation
    next suffix textEquation
  have continuation :=
    TokenKind.strictPrefixContinuationFor_of_canonical
      first.kind second.kind firstValid.1 secondValid.1
      next suffix textEquation
  cases firstKind : first.kind with
  | keywordFunction | keywordLet | keywordIf | keywordElse | keywordReturn =>
      simp only [TokenKind.StrictPrefixContinuationFor, firstKind] at continuation
      simp only [TokenMaximalFor, firstKind] at firstMaximal
      exact firstMaximal
        ⟨UInt8.ofNat next.toNat, nextByte,
          identifierContinueByte_of_character next continuation⟩
  | identifier text =>
      simp only [TokenKind.StrictPrefixContinuationFor, firstKind] at continuation
      simp only [TokenMaximalFor, firstKind] at firstMaximal
      exact firstMaximal
        ⟨UInt8.ofNat next.toNat, nextByte,
          identifierContinueByte_of_character next continuation⟩
  | decimal digits =>
      simp only [TokenKind.StrictPrefixContinuationFor, firstKind] at continuation
      simp only [TokenMaximalFor, firstKind] at firstMaximal
      rcases continuation with decimal | hexadecimal
      · exact firstMaximal.1
          ⟨UInt8.ofNat next.toNat, nextByte,
            decimalContinueByte_of_character next decimal⟩
      · rcases hexadecimal with
          ⟨digitsEquation, hexadecimalDigits,
            secondKind, nextEquation⟩
        apply firstMaximal.2 digitsEquation
        rw [startEquation]
        exact eligibleHexadecimalAt_of_validFor second file
          hexadecimalDigits secondValid secondKind
  | hexadecimal digits =>
      simp only [TokenKind.StrictPrefixContinuationFor, firstKind] at continuation
      simp only [TokenMaximalFor, firstKind] at firstMaximal
      exact firstMaximal
        ⟨UInt8.ofNat next.toNat, nextByte,
          hexadecimalContinueByte_of_character next continuation⟩
  | minus =>
      simp only [TokenKind.StrictPrefixContinuationFor, firstKind] at continuation
      simp only [TokenMaximalFor, firstKind] at firstMaximal
      rw [continuation] at nextByte
      exact firstMaximal (by simpa using nextByte)
  | equal | bang | less | greater =>
      simp only [TokenKind.StrictPrefixContinuationFor, firstKind] at continuation
      simp only [TokenMaximalFor, firstKind] at firstMaximal
      rw [continuation] at nextByte
      exact firstMaximal (by simpa using nextByte)
  | arrow | equalEqual | bangEqual | lessEqual | greaterEqual | plus | star |
    slash | percent | ampersand | caret | pipe | leftParen | rightParen |
    leftBrace | rightBrace | colon | semicolon | comma =>
      simp only [TokenKind.StrictPrefixContinuationFor, firstKind] at continuation

private theorem token_eq_of_start_eq_of_end_le
    (first second : Token)
    (file : SourceFile)
    (firstValid : first.ValidFor file)
    (secondValid : second.ValidFor file)
    (firstMaximal : TokenMaximalFor first file)
    (startEquation : first.span.startByte = second.span.startByte)
    (endLe : first.span.endByte ≤ second.span.endByte) :
    first = second := by
  rcases tokenTextCharPrefix_of_start_eq_of_end_le
      first second file firstValid secondValid startEquation endLe with
    ⟨suffix, textEquation⟩
  cases suffix with
  | nil =>
      simp only [List.append_nil] at textEquation
      have textsEqual : first.kind.text = second.kind.text :=
        String.toList_injective textEquation
      have kindsEqual := TokenKind.eq_of_canonical_of_text_eq
        first.kind second.kind firstValid.1 secondValid.1 textsEqual
      have firstLength := tokenSpanLength_eq_textLength first file firstValid
      have secondLength := tokenSpanLength_eq_textLength second file secondValid
      rw [kindsEqual, startEquation] at firstLength
      have endsEqual : first.span.endByte = second.span.endByte := by
        have firstOrdered := firstValid.2.1.1.2
        have secondOrdered := secondValid.2.1.1.2
        omega
      have spansEqual : first.span = second.span := by
        cases firstSpan : first.span
        cases secondSpan : second.span
        simp_all [Token.ValidFor, SourceSpan.ValidFor]
      exact Token.eq_of_validFor_of_span_eq
        first second file firstValid secondValid spansEqual
  | cons next suffix =>
      exact False.elim
        (strictTokenPrefix_contradicts_maximality
          first second file firstValid secondValid startEquation
          next suffix textEquation firstMaximal)

/-- Two valid maximal tokens beginning at the same byte are identical. -/
theorem token_eq_of_validFor_of_maximal_of_startByte_eq
    (first second : Token)
    (file : SourceFile)
    (firstValid : first.ValidFor file)
    (secondValid : second.ValidFor file)
    (firstMaximal : TokenMaximalFor first file)
    (secondMaximal : TokenMaximalFor second file)
    (startEquation : first.span.startByte = second.span.startByte) :
    first = second := by
  rcases Nat.le_total first.span.endByte second.span.endByte with
    endLe | endLe
  · exact token_eq_of_start_eq_of_end_le first second file
      firstValid secondValid firstMaximal startEquation endLe
  · exact (token_eq_of_start_eq_of_end_le second first file
      secondValid firstValid secondMaximal startEquation.symm endLe).symm

private theorem commentPayload_getElem?_eq_byteAt
    (comment : Comment)
    (file : SourceFile)
    (_valid : comment.ValidFor file)
    (index : Nat)
    (startLe : comment.span.startByte ≤ index)
    (indexLt : index < comment.span.endByte) :
    ((file.content.toByteArray.extract comment.span.startByte
      comment.span.endByte).data.toList)[index - comment.span.startByte]? =
      byteAt file index := by
  unfold byteAt
  rw [← Array.getElem?_toList]
  simp only [ByteArray.data_extract, Array.toList_extract]
  rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop]
  congr 1
  omega

private theorem validToken_validComment_start_ne
    (token : Token)
    (comment : Comment)
    (file : SourceFile)
    (tokenValid : token.ValidFor file)
    (commentValid : comment.ValidFor file)
    (tokenMaximal : TokenMaximalFor token file)
    (startEquation :
      token.span.startByte = comment.span.startByte) :
    False := by
  rcases Comment.validFor_payload_opener comment file commentValid with
    ⟨second, body, payloadEquation, openerKind⟩
  have payloadLengths := congrArg List.length payloadEquation
  simp only [Array.length_toList, List.length_cons] at payloadLengths
  have commentEndInBounds :
      comment.span.endByte ≤ file.content.toByteArray.size := by
    simpa using commentValid.1.2
  have payloadSize :
      (file.content.toByteArray.extract
        comment.span.startByte comment.span.endByte).size =
        comment.span.endByte - comment.span.startByte := by
    rw [ByteArray.size_extract, Nat.min_eq_left commentEndInBounds]
  have commentOrdered := commentValid.1.1.2
  have secondInComment :
      comment.span.startByte + 1 < comment.span.endByte := by
    change
      (file.content.toByteArray.extract
        comment.span.startByte comment.span.endByte).size = _ at payloadLengths
    rw [payloadSize] at payloadLengths
    omega
  have commentStartByte := commentPayload_getElem?_eq_byteAt
    comment file commentValid comment.span.startByte (by omega) (by omega)
  have commentSecondByte := commentPayload_getElem?_eq_byteAt
    comment file commentValid (comment.span.startByte + 1)
    (by omega) secondInComment
  rw [payloadEquation] at commentStartByte commentSecondByte
  simp at commentStartByte commentSecondByte
  have tokenOrdered := tokenValid.2.1.1.2
  have tokenNonempty := Token.validFor_startByte_lt_endByte
    token file tokenValid
  have tokenStartByte := tokenText_getElem?_eq_byteAt
    token file tokenValid token.span.startByte (by omega) tokenNonempty
  rw [startEquation, ← commentStartByte] at tokenStartByte
  simp at tokenStartByte
  have tokenStartByteList :
      token.kind.text.toByteArray.data.toList[0]? = some 47 := by
    simpa using tokenStartByte
  have tokenKind : token.kind = .slash :=
    TokenKind.eq_slash_of_canonical_of_firstByte
      token.kind tokenValid.1 tokenStartByteList
  have tokenLength := tokenSpanLength_eq_textLength token file tokenValid
  rw [tokenKind] at tokenLength
  simp [TokenKind.text] at tokenLength
  have tokenEnd :
      token.span.endByte = token.span.startByte + 1 := by
    omega
  simp only [TokenMaximalFor, tokenKind] at tokenMaximal
  rw [← startEquation, ← tokenEnd] at commentSecondByte
  rcases openerKind with line | block
  · rw [line.2] at commentSecondByte
    exact tokenMaximal.1 (by simpa using commentSecondByte.symm)
  · rw [block.2] at commentSecondByte
    exact tokenMaximal.2 (by simpa using commentSecondByte.symm)

/--
`Lexes file lexed` is the successful declarative lexical judgment.

The structural conjunct recognizes whitespace, every closed token form, line
comments, and properly nested block comments through exact source coverage.
The second conjunct makes every ambiguous token choice maximal. Consequently,
invalid characters and unterminated block comments have no successful
judgment: neither is an allowed uncovered byte, token payload, or valid
comment.
-/
def Lexes (file : SourceFile) (lexed : Lexed) : Prop :=
  lexed.ValidFor file ∧
    ∀ token ∈ lexed.tokens, TokenMaximalFor token file

/-- Executable decision procedure for the declarative lexical judgment. -/
def accepts (file : SourceFile) (lexed : Lexed) : Bool :=
  lexed.isValidFor file &&
    lexed.tokens.all fun token => tokenIsMaximalFor token file

theorem accepts_eq_true_iff
    (file : SourceFile)
    (lexed : Lexed) :
    accepts file lexed = true ↔ Lexes file lexed := by
  simp [accepts, Lexes, Lexed.isValidFor_eq_true_iff,
    tokenIsMaximalFor_eq_true_iff]

private inductive Element where
  | token (value : Token)
  | comment (value : Comment)
  deriving DecidableEq

namespace Element

def span : Element → SourceSpan
  | .token value => value.span
  | .comment value => value.span

def BelongsTo : Element → Lexed → Prop
  | .token value, lexed => value ∈ lexed.tokens
  | .comment value, lexed => value ∈ lexed.comments

def ValidFor (element : Element) (file : SourceFile) : Prop :=
  match element with
  | .token value => value.ValidFor file ∧ TokenMaximalFor value file
  | .comment value => value.ValidFor file

end Element

private theorem head_startByte_le_of_spansOrdered
    {Item : Type}
    (itemSpan : Item → SourceSpan)
    (head : Item)
    (tail : List Item)
    (ordered : Lexed.SpansOrdered ((head :: tail).map itemSpan))
    (wellFormed :
      ∀ item ∈ head :: tail,
        (itemSpan item).startByte ≤ (itemSpan item).endByte)
    (item : Item)
    (member : item ∈ head :: tail) :
    (itemSpan head).startByte ≤ (itemSpan item).startByte := by
  induction tail generalizing head with
  | nil =>
      simp at member
      subst item
      exact Nat.le_refl _
  | cons second rest inductionHypothesis =>
      simp only [List.map_cons, Lexed.SpansOrdered] at ordered
      simp only [List.mem_cons] at member
      rcases member with rfl | tailMember
      ·
        exact Nat.le_refl _
      · have headWellFormed := wellFormed head (by simp)
        have tailWellFormed :
            ∀ item ∈ second :: rest,
              (itemSpan item).startByte ≤ (itemSpan item).endByte := by
          intro item itemMember
          exact wellFormed item (by simp [itemMember])
        exact Nat.le_trans
          (Nat.le_trans headWellFormed ordered.1)
          (inductionHypothesis second ordered.2 tailWellFormed (by
            simpa only [List.mem_cons] using tailMember))

private theorem endByte_le_startByte_of_spansOrdered_of_startByte_lt
    {Item : Type}
    (itemSpan : Item → SourceSpan)
    (items : List Item)
    (ordered : Lexed.SpansOrdered (items.map itemSpan))
    (wellFormed :
      ∀ item ∈ items,
        (itemSpan item).startByte ≤ (itemSpan item).endByte)
    (first second : Item)
    (firstMember : first ∈ items)
    (secondMember : second ∈ items)
    (startLt :
      (itemSpan first).startByte < (itemSpan second).startByte) :
    (itemSpan first).endByte ≤ (itemSpan second).startByte := by
  induction items with
  | nil =>
      simp at firstMember
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at firstMember secondMember
      rcases firstMember with rfl | firstTail
      · rcases secondMember with rfl | secondTail
        · omega
        · cases tail with
          | nil => simp at secondTail
          | cons next rest =>
              simp only [List.map_cons, Lexed.SpansOrdered] at ordered
              have tailWellFormed :
                  ∀ item ∈ next :: rest,
                    (itemSpan item).startByte ≤
                      (itemSpan item).endByte := by
                intro item itemMember
                exact wellFormed item (by simp [itemMember])
              exact Nat.le_trans ordered.1
                (head_startByte_le_of_spansOrdered itemSpan next rest
                  ordered.2 tailWellFormed second secondTail)
      · rcases secondMember with rfl | secondTail
        · have headLeFirst := head_startByte_le_of_spansOrdered
            itemSpan second tail ordered wellFormed first (by
              simpa only [List.mem_cons] using Or.inr firstTail)
          omega
        · cases tail with
          | nil => simp at firstTail
          | cons next rest =>
              simp only [List.map_cons, Lexed.SpansOrdered] at ordered
              have tailWellFormed :
                  ∀ item ∈ next :: rest,
                    (itemSpan item).startByte ≤
                      (itemSpan item).endByte := by
                intro item itemMember
                exact wellFormed item (by simp [itemMember])
              exact inductionHypothesis ordered.2 tailWellFormed
                firstTail secondTail

private theorem spansOrdered_map_tail
    {Item : Type}
    (itemSpan : Item → SourceSpan)
    (head : Item)
    (tail : List Item)
    (ordered : Lexed.SpansOrdered ((head :: tail).map itemSpan)) :
    Lexed.SpansOrdered (tail.map itemSpan) := by
  cases tail with
  | nil => simp [Lexed.SpansOrdered]
  | cons second rest =>
      simpa only [List.map_cons, Lexed.SpansOrdered] using ordered.2

private theorem head_startByte_lt_of_spansOrdered_of_mem_tail
    {Item : Type}
    (itemSpan : Item → SourceSpan)
    (head : Item)
    (tail : List Item)
    (ordered : Lexed.SpansOrdered ((head :: tail).map itemSpan))
    (nonempty :
      ∀ item ∈ head :: tail,
        (itemSpan item).startByte < (itemSpan item).endByte)
    (item : Item)
    (member : item ∈ tail) :
    (itemSpan head).startByte < (itemSpan item).startByte := by
  cases tail with
  | nil => simp at member
  | cons second rest =>
      simp only [List.map_cons, Lexed.SpansOrdered] at ordered
      have tailNonempty :
          ∀ item ∈ second :: rest,
            (itemSpan item).startByte < (itemSpan item).endByte := by
        intro item itemMember
        exact nonempty item (by simp [itemMember])
      have secondLeItem := head_startByte_le_of_spansOrdered
        itemSpan second rest ordered.2
        (fun item itemMember => Nat.le_of_lt
          (tailNonempty item itemMember))
        item member
      have headNonempty := nonempty head (by simp)
      omega

private theorem list_eq_of_spansOrdered_of_same_members
    {Item : Type}
    (itemSpan : Item → SourceSpan)
    (first second : List Item)
    (firstOrdered : Lexed.SpansOrdered (first.map itemSpan))
    (secondOrdered : Lexed.SpansOrdered (second.map itemSpan))
    (firstNonempty :
      ∀ item ∈ first,
        (itemSpan item).startByte < (itemSpan item).endByte)
    (secondNonempty :
      ∀ item ∈ second,
        (itemSpan item).startByte < (itemSpan item).endByte)
    (sameMembers : ∀ item, item ∈ first ↔ item ∈ second)
    (eqOfStartByteEq :
      ∀ firstItem ∈ first, ∀ secondItem ∈ second,
        (itemSpan firstItem).startByte =
            (itemSpan secondItem).startByte →
          firstItem = secondItem) :
    first = second := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons head tail =>
          have headMember := (sameMembers head).mpr (by simp)
          simp at headMember
  | cons firstHead firstTail inductionHypothesis =>
      cases second with
      | nil =>
          have headMember := (sameMembers firstHead).mp (by simp)
          simp at headMember
      | cons secondHead secondTail =>
          have firstHeadInSecond :
              firstHead ∈ secondHead :: secondTail :=
            (sameMembers firstHead).mp (by simp)
          have secondHeadInFirst :
              secondHead ∈ firstHead :: firstTail :=
            (sameMembers secondHead).mpr (by simp)
          have firstWellFormed :
              ∀ item ∈ firstHead :: firstTail,
                (itemSpan item).startByte ≤
                  (itemSpan item).endByte := by
            intro item member
            exact Nat.le_of_lt (firstNonempty item member)
          have secondWellFormed :
              ∀ item ∈ secondHead :: secondTail,
                (itemSpan item).startByte ≤
                  (itemSpan item).endByte := by
            intro item member
            exact Nat.le_of_lt (secondNonempty item member)
          have firstStartLeSecondStart :=
            head_startByte_le_of_spansOrdered itemSpan
              firstHead firstTail firstOrdered firstWellFormed
              secondHead secondHeadInFirst
          have secondStartLeFirstStart :=
            head_startByte_le_of_spansOrdered itemSpan
              secondHead secondTail secondOrdered secondWellFormed
              firstHead firstHeadInSecond
          have startEquation :
              (itemSpan firstHead).startByte =
                (itemSpan secondHead).startByte :=
            Nat.le_antisymm firstStartLeSecondStart
              secondStartLeFirstStart
          have headEquation := eqOfStartByteEq
            firstHead (by simp) secondHead (by simp) startEquation
          subst secondHead
          congr 1
          apply inductionHypothesis
          · exact spansOrdered_map_tail itemSpan
              firstHead firstTail firstOrdered
          · exact spansOrdered_map_tail itemSpan
              firstHead secondTail secondOrdered
          · intro item member
            exact firstNonempty item (by simp [member])
          · intro item member
            exact secondNonempty item (by simp [member])
          · intro item
            have firstHeadNotInFirstTail : firstHead ∉ firstTail := by
              intro member
              have strict :=
                head_startByte_lt_of_spansOrdered_of_mem_tail
                  itemSpan firstHead firstTail firstOrdered
                  firstNonempty firstHead member
              omega
            have firstHeadNotInSecondTail : firstHead ∉ secondTail := by
              intro member
              have strict :=
                head_startByte_lt_of_spansOrdered_of_mem_tail
                  itemSpan firstHead secondTail secondOrdered
                  secondNonempty firstHead member
              omega
            by_cases itemEquation : item = firstHead
            · subst item
              simp [firstHeadNotInFirstTail, firstHeadNotInSecondTail]
            · simpa [itemEquation] using sameMembers item
          · intro firstItem firstMember secondItem secondMember
              startEquation
            exact eqOfStartByteEq firstItem (by simp [firstMember])
              secondItem (by simp [secondMember]) startEquation

private theorem element_validFor_of_belongsTo
    (element : Element)
    (file : SourceFile)
    (lexed : Lexed)
    (lexes : Lexes file lexed)
    (belongs : element.BelongsTo lexed) :
    element.ValidFor file := by
  rcases lexes with ⟨valid, maximal⟩
  rcases valid with
    ⟨tokensValid, commentsValid, tokensOrdered, commentsOrdered,
      crossDisjoint, partitioned⟩
  cases element with
  | token token => exact ⟨tokensValid token belongs, maximal token belongs⟩
  | comment comment => exact commentsValid comment belongs

private theorem element_startByte_lt_endByte_of_validFor
    (element : Element)
    (file : SourceFile)
    (valid : element.ValidFor file) :
    element.span.startByte < element.span.endByte := by
  cases element with
  | token token =>
      exact Token.validFor_startByte_lt_endByte token file valid.1
  | comment comment =>
      exact Comment.validFor_startByte_lt_endByte comment file valid

private theorem element_startByte_not_asciiWhitespace
    (element : Element)
    (file : SourceFile)
    (valid : element.ValidFor file)
    (byte : UInt8)
    (sourceByte :
      file.content.toByteArray.data[element.span.startByte]? = some byte)
    (whitespace : Lexed.IsAsciiWhitespaceByte byte) :
    False := by
  have byteGe : 33 ≤ byte.toNat := by
    cases element with
    | token token =>
        simp only [Element.ValidFor, Element.span] at valid sourceByte
        have nonempty := Token.validFor_startByte_lt_endByte
          token file valid.1
        have firstByte := tokenText_getElem?_eq_byteAt
          token file valid.1 token.span.startByte (by omega) nonempty
        rw [show token.span.startByte - token.span.startByte = 0 by omega,
          byteAt, sourceByte] at firstByte
        exact TokenKind.canonical_text_firstByte_toNat_ge
          token.kind valid.1.1 byte firstByte
    | comment comment =>
        simp only [Element.ValidFor, Element.span] at valid sourceByte
        rcases Comment.validFor_payload_opener comment file valid with
          ⟨second, body, payloadEquation, openerKind⟩
        have commentStart := commentPayload_getElem?_eq_byteAt
          comment file valid comment.span.startByte (by omega)
          (Comment.validFor_startByte_lt_endByte comment file valid)
        rw [payloadEquation] at commentStart
        simp at commentStart
        rw [byteAt, sourceByte] at commentStart
        have byteEquation : byte = 47 := by
          simpa using commentStart.symm
        rw [byteEquation]
        decide
  rcases whitespace with
    rfl | rfl | rfl | rfl | rfl <;>
      simp [UInt8.toNat_ofNat] at byteGe

private theorem element_endByte_le_startByte_of_startByte_lt
    (first second : Element)
    (file : SourceFile)
    (lexed : Lexed)
    (lexes : Lexes file lexed)
    (firstBelongs : first.BelongsTo lexed)
    (secondBelongs : second.BelongsTo lexed)
    (startLt : first.span.startByte < second.span.startByte) :
    first.span.endByte ≤ second.span.startByte := by
  rcases lexes.1 with
    ⟨tokensValid, commentsValid, tokensOrdered, commentsOrdered,
      crossDisjoint, partitioned⟩
  cases first with
  | token firstToken =>
      cases second with
      | token secondToken =>
          simp only [Element.span] at startLt ⊢
          apply endByte_le_startByte_of_spansOrdered_of_startByte_lt
            (fun token : Token => token.span) lexed.tokens tokensOrdered
          · intro token member
            exact (tokensValid token member).2.1.1.2
          · exact firstBelongs
          · exact secondBelongs
          · exact startLt
      | comment secondComment =>
          simp only [Element.span] at startLt ⊢
          rcases crossDisjoint firstToken firstBelongs
            secondComment secondBelongs with before | after
          · exact before
          · have secondValid := commentsValid secondComment secondBelongs
            have secondNonempty :=
              Comment.validFor_startByte_lt_endByte
                secondComment file secondValid
            omega
  | comment firstComment =>
      cases second with
      | token secondToken =>
          simp only [Element.span] at startLt ⊢
          rcases crossDisjoint secondToken secondBelongs
            firstComment firstBelongs with after | before
          · have secondValid := tokensValid secondToken secondBelongs
            have secondNonempty :=
              Token.validFor_startByte_lt_endByte
                secondToken file secondValid
            omega
          · exact before
      | comment secondComment =>
          simp only [Element.span] at startLt ⊢
          apply endByte_le_startByte_of_spansOrdered_of_startByte_lt
            (fun comment : Comment => comment.span)
            lexed.comments commentsOrdered
          · intro comment member
            exact (commentsValid comment member).1.1.2
          · exact firstBelongs
          · exact secondBelongs
          · exact startLt

private theorem element_endByte_le_sourceSize_of_validFor
    (element : Element)
    (file : SourceFile)
    (valid : element.ValidFor file) :
    element.span.endByte ≤ file.content.toByteArray.size := by
  cases element with
  | token token =>
      exact valid.1.2.1.2
  | comment comment =>
      exact valid.1.2

private theorem element_or_asciiWhitespace_at
    (file : SourceFile)
    (lexed : Lexed)
    (lexes : Lexes file lexed)
    (index : Nat)
    (inBounds : index < file.content.toByteArray.size) :
    (∃ element : Element,
      Element.BelongsTo element lexed ∧
        Lexed.CoversByte (Element.span element) index) ∨
    ∃ byte,
      file.content.toByteArray.data[index]? = some byte ∧
        Lexed.IsAsciiWhitespaceByte byte := by
  rcases lexes.1 with
    ⟨tokensValid, commentsValid, tokensOrdered, commentsOrdered,
      crossDisjoint, partitioned⟩
  rcases partitioned index inBounds with
    ⟨token, member, covered⟩ |
    ⟨comment, member, covered⟩ |
    ⟨byte, sourceByte, whitespace⟩
  · exact Or.inl ⟨Element.token token, member, covered⟩
  · exact Or.inl ⟨Element.comment comment, member, covered⟩
  · exact Or.inr ⟨byte, sourceByte, whitespace⟩

private theorem element_eq_of_validFor_of_startByte_eq
    (first second : Element)
    (file : SourceFile)
    (firstValid : first.ValidFor file)
    (secondValid : second.ValidFor file)
    (startEquation :
      first.span.startByte = second.span.startByte) :
    first = second := by
  cases first with
  | token firstToken =>
      cases second with
      | token secondToken =>
          simp only [Element.ValidFor, Element.span] at firstValid secondValid startEquation
          exact congrArg Element.token
            (token_eq_of_validFor_of_maximal_of_startByte_eq
              firstToken secondToken file firstValid.1 secondValid.1
              firstValid.2 secondValid.2 startEquation)
      | comment secondComment =>
          simp only [Element.ValidFor, Element.span] at firstValid secondValid startEquation
          exact False.elim (validToken_validComment_start_ne
            firstToken secondComment file firstValid.1 secondValid
            firstValid.2 startEquation)
  | comment firstComment =>
      cases second with
      | token secondToken =>
          simp only [Element.ValidFor, Element.span] at firstValid secondValid startEquation
          exact False.elim (validToken_validComment_start_ne
            secondToken firstComment file secondValid.1 firstValid
            secondValid.2 startEquation.symm)
      | comment secondComment =>
          simp only [Element.ValidFor, Element.span] at firstValid secondValid startEquation
          exact congrArg Element.comment
            (Comment.eq_of_validFor_of_startByte_eq
              firstComment secondComment file firstValid secondValid
              startEquation)

private theorem element_belongsTo_iff_of_lexes
    (file : SourceFile)
    (first second : Lexed)
    (firstLexes : Lexes file first)
    (secondLexes : Lexes file second)
    (element : Element) :
    element.BelongsTo first ↔ element.BelongsTo second := by
  have agreement :
      ∀ offset (element : Element),
        (Element.span element).startByte = offset →
          (Element.BelongsTo element first ↔
            Element.BelongsTo element second) := by
    intro offset
    induction offset using Nat.strongRecOn with
    | ind offset inductionHypothesis =>
        intro element startEquation
        constructor
        · intro firstBelongs
          have elementValid := element_validFor_of_belongsTo
            element file first firstLexes firstBelongs
          have elementNonempty :=
            element_startByte_lt_endByte_of_validFor
              element file elementValid
          have elementEndInBounds :=
            element_endByte_le_sourceSize_of_validFor
              element file elementValid
          have offsetInBounds :
              offset < file.content.toByteArray.size := by
            omega
          rcases element_or_asciiWhitespace_at
              file second secondLexes offset offsetInBounds with
            ⟨other, otherBelongs, covered⟩ |
            ⟨byte, sourceByte, whitespace⟩
          · by_cases sameStart : other.span.startByte = offset
            · have otherValid := element_validFor_of_belongsTo
                other file second secondLexes otherBelongs
              have elementEquation :=
                element_eq_of_validFor_of_startByte_eq
                  element other file elementValid otherValid
                    (startEquation.trans sameStart.symm)
              rw [elementEquation]
              exact otherBelongs
            · have otherStartLt : other.span.startByte < offset := by
                rcases covered with ⟨startLe, indexLt⟩
                omega
              have otherBelongsFirst :=
                (inductionHypothesis other.span.startByte otherStartLt
                  other rfl).mpr otherBelongs
              have separated :=
                element_endByte_le_startByte_of_startByte_lt
                  other element file first firstLexes
                  otherBelongsFirst firstBelongs (by omega)
              exact False.elim (by
                rcases covered with ⟨startLe, indexLt⟩
                omega)
          · exact False.elim
              (element_startByte_not_asciiWhitespace
                element file elementValid byte (by
                  simpa [startEquation] using sourceByte) whitespace)
        · intro secondBelongs
          have elementValid := element_validFor_of_belongsTo
            element file second secondLexes secondBelongs
          have elementNonempty :=
            element_startByte_lt_endByte_of_validFor
              element file elementValid
          have elementEndInBounds :=
            element_endByte_le_sourceSize_of_validFor
              element file elementValid
          have offsetInBounds :
              offset < file.content.toByteArray.size := by
            omega
          rcases element_or_asciiWhitespace_at
              file first firstLexes offset offsetInBounds with
            ⟨other, otherBelongs, covered⟩ |
            ⟨byte, sourceByte, whitespace⟩
          · by_cases sameStart : other.span.startByte = offset
            · have otherValid := element_validFor_of_belongsTo
                other file first firstLexes otherBelongs
              have elementEquation :=
                element_eq_of_validFor_of_startByte_eq
                  element other file elementValid otherValid
                    (startEquation.trans sameStart.symm)
              rw [elementEquation]
              exact otherBelongs
            · have otherStartLt : other.span.startByte < offset := by
                rcases covered with ⟨startLe, indexLt⟩
                omega
              have otherBelongsSecond :=
                (inductionHypothesis other.span.startByte otherStartLt
                  other rfl).mp otherBelongs
              have separated :=
                element_endByte_le_startByte_of_startByte_lt
                  other element file second secondLexes
                  otherBelongsSecond secondBelongs (by omega)
              exact False.elim (by
                rcases covered with ⟨startLe, indexLt⟩
                omega)
          · exact False.elim
              (element_startByte_not_asciiWhitespace
                element file elementValid byte (by
                  simpa [startEquation] using sourceByte) whitespace)
  exact agreement element.span.startByte element rfl

/-- Successful declarative lexing has a unique token-and-comment output. -/
theorem eq_of_lexes
    (file : SourceFile)
    (first second : Lexed)
    (firstLexes : Lexes file first)
    (secondLexes : Lexes file second) :
    first = second := by
  rcases firstLexes.1 with
    ⟨firstTokensValid, firstCommentsValid,
      firstTokensOrdered, firstCommentsOrdered,
      firstCrossDisjoint, firstPartitioned⟩
  rcases secondLexes.1 with
    ⟨secondTokensValid, secondCommentsValid,
      secondTokensOrdered, secondCommentsOrdered,
      secondCrossDisjoint, secondPartitioned⟩
  have tokensEquation : first.tokens = second.tokens := by
    apply list_eq_of_spansOrdered_of_same_members
      (fun token : Token => token.span)
      first.tokens second.tokens firstTokensOrdered secondTokensOrdered
    · intro token member
      exact Token.validFor_startByte_lt_endByte token file
        (firstTokensValid token member)
    · intro token member
      exact Token.validFor_startByte_lt_endByte token file
        (secondTokensValid token member)
    · intro token
      simpa only [Element.BelongsTo] using
        (element_belongsTo_iff_of_lexes file first second
          firstLexes secondLexes (Element.token token))
    · intro firstToken firstMember secondToken secondMember
        startEquation
      exact token_eq_of_validFor_of_maximal_of_startByte_eq
        firstToken secondToken file
        (firstTokensValid firstToken firstMember)
        (secondTokensValid secondToken secondMember)
        (firstLexes.2 firstToken firstMember)
        (secondLexes.2 secondToken secondMember)
        startEquation
  have commentsEquation : first.comments = second.comments := by
    apply list_eq_of_spansOrdered_of_same_members
      (fun comment : Comment => comment.span)
      first.comments second.comments
      firstCommentsOrdered secondCommentsOrdered
    · intro comment member
      exact Comment.validFor_startByte_lt_endByte comment file
        (firstCommentsValid comment member)
    · intro comment member
      exact Comment.validFor_startByte_lt_endByte comment file
        (secondCommentsValid comment member)
    · intro comment
      simpa only [Element.BelongsTo] using
        (element_belongsTo_iff_of_lexes file first second
          firstLexes secondLexes (Element.comment comment))
    · intro firstComment firstMember secondComment secondMember
        startEquation
      exact Comment.eq_of_validFor_of_startByte_eq
        firstComment secondComment file
        (firstCommentsValid firstComment firstMember)
        (secondCommentsValid secondComment secondMember)
        startEquation
  cases first
  cases second
  simp_all

/--
Return the character suffix that starts at an exact UTF-8 byte boundary.
Offsets inside a multi-byte character are rejected.
-/
private def charactersAtByteOffset :
    List Char → Nat → Option (List Char)
  | characters, 0 => some characters
  | [], _ + 1 => none
  | character :: rest, offset + 1 =>
      if character.utf8Size ≤ offset + 1 then
        charactersAtByteOffset rest (offset + 1 - character.utf8Size)
      else
        none

theorem charactersAtByteOffset_prefix
    (leading trailing : List Char) :
    charactersAtByteOffset (leading ++ trailing)
        (String.ofList leading).utf8ByteSize = some trailing := by
  induction leading with
  | nil =>
      simp [charactersAtByteOffset]
  | cons character rest inductionHypothesis =>
      rw [String.ofList_cons, String.utf8ByteSize_append,
        String.utf8ByteSize_singleton]
      have positive := Char.utf8Size_pos character
      simp only [List.cons_append]
      cases sizeEquation : character.utf8Size with
      | zero =>
          omega
      | succ size =>
          rw [show
            size + 1 + (String.ofList rest).utf8ByteSize =
              (size + (String.ofList rest).utf8ByteSize) + 1 by omega]
          rw [charactersAtByteOffset]
          rw [if_pos (by omega)]
          rw [show
            size + (String.ofList rest).utf8ByteSize + 1 -
                character.utf8Size =
              (String.ofList rest).utf8ByteSize by omega]
          exact inductionHypothesis

private def isWhitespaceCharacter (character : Char) : Bool :=
  character = ' ' ||
    character = '\t' ||
    character = '\r' ||
    character = '\n' ||
    character.toNat == 12

private def isAsciiLowerCharacter (character : Char) : Bool :=
  'a' ≤ character && character ≤ 'z'

private def isAsciiUpperCharacter (character : Char) : Bool :=
  'A' ≤ character && character ≤ 'Z'

private def isAsciiDigitCharacter (character : Char) : Bool :=
  '0' ≤ character && character ≤ '9'

private def canStartToken (character : Char) : Bool :=
  isAsciiLowerCharacter character ||
    isAsciiUpperCharacter character ||
    isAsciiDigitCharacter character ||
    character = '=' ||
    character = '!' ||
    character = '<' ||
    character = '>' ||
    character = '+' ||
    character = '-' ||
    character = '*' ||
    character = '/' ||
    character = '%' ||
    character = '&' ||
    character = '^' ||
    character = '|' ||
    character = '(' ||
    character = ')' ||
    character = '{' ||
    character = '}' ||
    character = ':' ||
    character = ';' ||
    character = ','

/--
Recognize whether a nested block-comment body reaches its matching close.
The input starts immediately after the outer `/*`.
-/
private def blockCommentCloses : List Char → Nat → Bool
  | [], _ => false
  | '/' :: '*' :: rest, depth =>
      blockCommentCloses rest (depth + 1)
  | '*' :: '/' :: rest, depth =>
      if depth == 1 then
        true
      else
        blockCommentCloses rest (depth - 1)
  | _ :: rest, depth =>
      blockCommentCloses rest depth

theorem blockCommentCloses_equation
    (characters : List Char)
    (depth : Nat) :
    blockCommentCloses characters depth =
      match characters with
      | [] => false
      | '/' :: '*' :: rest => blockCommentCloses rest (depth + 1)
      | '*' :: '/' :: rest =>
          if depth == 1 then true else blockCommentCloses rest (depth - 1)
      | _ :: rest => blockCommentCloses rest depth := by
  rw [blockCommentCloses.eq_def]
  cases characters with
  | nil =>
      rfl
  | cons first rest =>
      cases rest with
      | nil =>
          by_cases firstSlash : first = '/'
          · subst first
            rfl
          · by_cases firstStar : first = '*'
            · subst first
              rfl
            · simp
      | cons second trailing =>
          by_cases firstSlash : first = '/'
          · subst first
            by_cases secondStar : second = '*'
            · subst second
              rfl
            · simp [secondStar]
          · by_cases firstStar : first = '*'
            · subst first
              by_cases secondSlash : second = '/'
              · subst second
                rfl
              · simp [firstSlash, secondSlash]
            · simp [firstSlash, firstStar]

private def invalidCharacterRejection
    (file : SourceFile)
    (offset : Nat)
    (character : Char) : LexError := {
  code := "SL0001"
  span := {
    source := file.path
    startByte := offset
    endByte := offset + character.utf8Size
  }
  kind := .invalidCharacter character
}

private def unterminatedBlockCommentRejection
    (file : SourceFile)
    (offset : Nat) : LexError := {
  code := "SL0002"
  span := {
    source := file.path
    startByte := offset
    endByte := file.content.utf8ByteSize
  }
  kind := .unterminatedBlockComment
}

/--
A declarative source rejection at a lexer cursor.

The caller supplies a byte offset reached after recognizing a valid prefix.
The judgment then distinguishes an unsupported character from an unterminated
nested block comment and fixes the public error code and UTF-8 span.
-/
inductive RejectsAt
    (file : SourceFile)
    (offset : Nat) :
    LexError → Prop where
  | invalidCharacter
      (character : Char)
      (remaining : List Char)
      (atCursor :
        charactersAtByteOffset file.content.toList offset =
          some (character :: remaining))
      (notWhitespace : isWhitespaceCharacter character = false)
      (cannotStart : canStartToken character = false) :
      RejectsAt file offset
        (invalidCharacterRejection file offset character)
  | unterminatedBlockComment
      (remaining : List Char)
      (atCursor :
        charactersAtByteOffset file.content.toList offset =
          some ('/' :: '*' :: remaining))
      (unterminated : blockCommentCloses remaining 1 = false) :
      RejectsAt file offset (unterminatedBlockCommentRejection file offset)

/-- Executable decision procedure for `RejectsAt` at a known lexer cursor. -/
def failureAt (file : SourceFile) (offset : Nat) : Option LexError :=
  match charactersAtByteOffset file.content.toList offset with
  | some (character :: remaining) =>
      if isWhitespaceCharacter character || canStartToken character then
        match character, remaining with
        | '/', '*' :: body =>
            if blockCommentCloses body 1 then
              none
            else
              some (unterminatedBlockCommentRejection file offset)
        | _, _ =>
            none
      else
        some (invalidCharacterRejection file offset character)
  | _ =>
      none

theorem failureAt_eq_some_iff
    (file : SourceFile)
    (offset : Nat)
    (rejection : LexError) :
    failureAt file offset = some rejection ↔
      RejectsAt file offset rejection := by
  constructor
  · intro detected
    unfold failureAt at detected
    generalize suffixEquation :
      charactersAtByteOffset file.content.toList offset = suffix at detected
    cases suffix with
    | none =>
        contradiction
    | some characters =>
      cases characters with
      | nil =>
          contradiction
      | cons character remaining =>
        by_cases recognized :
            (isWhitespaceCharacter character ||
              canStartToken character) = true
        · simp [recognized] at detected
          by_cases slash : character = '/'
          · subst character
            cases remaining with
            | nil =>
                contradiction
            | cons next body =>
              by_cases star : next = '*'
              · subst next
                by_cases closes :
                    blockCommentCloses body 1 = true
                · simp [closes] at detected
                · have unterminated :
                      blockCommentCloses body 1 = false :=
                    (bool_eq_false_iff_not_eq_true _).2 closes
                  simp [unterminated] at detected
                  cases detected
                  exact .unterminatedBlockComment body
                    suffixEquation unterminated
              · simp [star] at detected
          · simp [slash] at detected
        · simp [recognized] at detected
          cases detected
          have classesFalse :
              isWhitespaceCharacter character = false ∧
                canStartToken character = false := by
            cases whitespace :
                isWhitespaceCharacter character <;>
              cases starts :
                canStartToken character <;>
              simp_all
          exact .invalidCharacter character remaining suffixEquation
            classesFalse.1 classesFalse.2
  · intro judgment
    cases judgment with
    | invalidCharacter character remaining atCursor notWhitespace cannotStart =>
        simp [failureAt, atCursor, notWhitespace, cannotStart]
    | unterminatedBlockComment remaining atCursor unterminated =>
        simp [failureAt, atCursor, canStartToken, unterminated]

theorem lexes_valid
    (file : SourceFile)
    (lexed : Lexed)
    (judgment : Lexes file lexed) :
    lexed.ValidFor file :=
  judgment.1

end LexicalGrammar

end Solcore.Surface
