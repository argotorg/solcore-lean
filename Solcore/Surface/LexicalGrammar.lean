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
