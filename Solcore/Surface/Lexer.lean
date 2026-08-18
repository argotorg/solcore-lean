import Solcore.Surface.LexicalGrammar

set_option autoImplicit false

namespace Solcore.Surface

inductive LexerInvariant where
  | fuelExhausted (span : SourceSpan)
  | invalidOutput (lexed : Lexed)
  deriving Repr, BEq

inductive LexFailure where
  | source (error : LexError)
  | internal (invariant : LexerInvariant)
  deriving Repr, BEq

namespace Lexer

private def sourceSpan (file : SourceFile) (startByte endByte : Nat) : SourceSpan := {
  source := file.path
  startByte
  endByte
}

private def isWhitespace (character : Char) : Bool :=
  character = ' ' ||
    character = '\t' ||
    character = '\r' ||
    character = '\n' ||
    character.toNat == 12

private def isAsciiLower (character : Char) : Bool :=
  'a' ≤ character && character ≤ 'z'

private def isAsciiUpper (character : Char) : Bool :=
  'A' ≤ character && character ≤ 'Z'

private def isAsciiDigit (character : Char) : Bool :=
  '0' ≤ character && character ≤ '9'

private def isAsciiHexDigit (character : Char) : Bool :=
  isAsciiDigit character ||
    ('a' ≤ character && character ≤ 'f') ||
    ('A' ≤ character && character ≤ 'F')

private def isIdentifierStart (character : Char) : Bool :=
  isAsciiLower character || isAsciiUpper character

private def isIdentifierContinue (character : Char) : Bool :=
  isIdentifierStart character || isAsciiDigit character || character = '_'

private def canStartToken (character : Char) : Bool :=
  isIdentifierStart character ||
    isAsciiDigit character ||
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

private def charactersByteSize (characters : List Char) : Nat :=
  characters.foldl (fun size character => size + character.utf8Size) 0

private theorem foldl_character_byte_size
    (initial : Nat)
    (characters : List Char) :
    characters.foldl (fun size character => size + character.utf8Size)
        initial =
      initial +
        characters.foldl
          (fun size character => size + character.utf8Size) 0 := by
  induction characters generalizing initial with
  | nil =>
      simp
  | cons character rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis (initial + character.utf8Size)]
      simp only [Nat.zero_add]
      rw [inductionHypothesis character.utf8Size]
      omega

private theorem charactersByteSize_cons
    (character : Char)
    (characters : List Char) :
    charactersByteSize (character :: characters) =
      character.utf8Size + charactersByteSize characters := by
  unfold charactersByteSize
  simp only [List.foldl_cons]
  rw [foldl_character_byte_size]
  simp

private theorem charactersByteSize_append
    (leading trailing : List Char) :
    charactersByteSize (leading ++ trailing) =
      charactersByteSize leading + charactersByteSize trailing := by
  induction leading with
  | nil =>
      simp [charactersByteSize]
  | cons character rest inductionHypothesis =>
      simp only [List.cons_append, charactersByteSize_cons,
        inductionHypothesis]
      omega

private theorem stringOfListByteSize_eq_charactersByteSize
    (characters : List Char) :
    (String.ofList characters).utf8ByteSize =
      charactersByteSize characters := by
  induction characters with
  | nil =>
      simp [charactersByteSize]
  | cons character rest inductionHypothesis =>
      simp only [String.ofList_cons, String.utf8ByteSize_append,
        String.utf8ByteSize_singleton, charactersByteSize_cons,
        inductionHypothesis]

private theorem stringByteSize_eq_charactersByteSize
    (text : String) :
    text.utf8ByteSize = charactersByteSize text.toList := by
  rw [← stringOfListByteSize_eq_charactersByteSize text.toList]
  exact congrArg String.utf8ByteSize String.ofList_toList.symm

private def sourceByteAt (file : SourceFile) (offset : Nat) : Option UInt8 :=
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

private def ImplementationIdentifierContinuesAt
    (file : SourceFile)
    (offset : Nat) : Prop :=
  ∃ byte,
    sourceByteAt file offset = some byte ∧
      isIdentifierContinueByte byte = true

private def ImplementationDecimalContinuesAt
    (file : SourceFile)
    (offset : Nat) : Prop :=
  ∃ byte,
    sourceByteAt file offset = some byte ∧
      isAsciiDigitByte byte = true

private def ImplementationHexadecimalContinuesAt
    (file : SourceFile)
    (offset : Nat) : Prop :=
  ∃ byte,
    sourceByteAt file offset = some byte ∧
      isAsciiHexDigitByte byte = true

private def ImplementationEligibleHexadecimalAt
    (file : SourceFile)
    (offset : Nat) : Prop :=
  sourceByteAt file offset = some 48 ∧
    sourceByteAt file (offset + 1) = some 120 ∧
    ImplementationHexadecimalContinuesAt file (offset + 2)

private def ImplementationTokenMaximalFor
    (value : Token)
    (file : SourceFile) : Prop :=
  let next := value.span.endByte
  match value.kind with
  | .keywordFunction
  | .keywordLet
  | .keywordIf
  | .keywordElse
  | .keywordReturn
  | .identifier _ =>
      ¬ ImplementationIdentifierContinuesAt file next
  | .decimal digits =>
      ¬ ImplementationDecimalContinuesAt file next ∧
        (digits = "0" →
          ¬ ImplementationEligibleHexadecimalAt file value.span.startByte)
  | .hexadecimal _ =>
      ¬ ImplementationHexadecimalContinuesAt file next
  | .minus =>
      sourceByteAt file next ≠ some 62
  | .equal =>
      sourceByteAt file next ≠ some 61
  | .bang =>
      sourceByteAt file next ≠ some 61
  | .less =>
      sourceByteAt file next ≠ some 61
  | .greater =>
      sourceByteAt file next ≠ some 61
  | .slash =>
      sourceByteAt file next ≠ some 47 ∧
        sourceByteAt file next ≠ some 42
  | _ => True

private def utf8FirstByte (character : Char) : UInt8 :=
  let value := character.val.toNat
  if value ≤ 127 then
    UInt8.ofNat value
  else if value ≤ 2047 then
    UInt8.ofNat (value / 64 % 32 + 192)
  else if value ≤ 65535 then
    UInt8.ofNat (value / 4096 % 16 + 224)
  else
    UInt8.ofNat (value / 262144 % 8 + 240)

private theorem utf8FirstByte_toNat_of_ascii
    (character : Char)
    (ascii : character.toNat ≤ 127) :
    (utf8FirstByte character).toNat = character.toNat := by
  change character.val.toNat ≤ 127 at ascii
  simp only [utf8FirstByte]
  rw [if_pos ascii]
  change character.val.toNat % 2 ^ 8 = character.val.toNat
  rw [show 2 ^ 8 = 256 by decide]
  exact Nat.mod_eq_of_lt (by omega)

private theorem utf8FirstByte_toNat_gt_ascii
    (character : Char)
    (notAscii : ¬ character.toNat ≤ 127) :
    127 < (utf8FirstByte character).toNat := by
  change ¬ character.val.toNat ≤ 127 at notAscii
  simp only [utf8FirstByte]
  rw [if_neg notAscii]
  split
  · have modulusBound : character.val.toNat / 64 % 32 < 32 :=
      Nat.mod_lt _ (by omega)
    have encodedBound :
        character.val.toNat / 64 % 32 + 192 < 256 := by
      omega
    change 127 < (character.val.toNat / 64 % 32 + 192) % 2 ^ 8
    rw [show 2 ^ 8 = 256 by decide,
      Nat.mod_eq_of_lt encodedBound]
    omega
  · split
    · have modulusBound :
          character.val.toNat / 4096 % 16 < 16 :=
        Nat.mod_lt _ (by omega)
      have encodedBound :
          character.val.toNat / 4096 % 16 + 224 < 256 := by
        omega
      change
        127 < (character.val.toNat / 4096 % 16 + 224) % 2 ^ 8
      rw [show 2 ^ 8 = 256 by decide,
        Nat.mod_eq_of_lt encodedBound]
      omega
    · have modulusBound :
          character.val.toNat / 262144 % 8 < 8 :=
        Nat.mod_lt _ (by omega)
      have encodedBound :
          character.val.toNat / 262144 % 8 + 240 < 256 := by
        omega
      change
        127 < (character.val.toNat / 262144 % 8 + 240) % 2 ^ 8
      rw [show 2 ^ 8 = 256 by decide,
        Nat.mod_eq_of_lt encodedBound]
      omega

private theorem utf8FirstByte_range_iff
    (character : Char)
    (lower upper : Nat)
    (upperAscii : upper ≤ 127) :
    (lower ≤ (utf8FirstByte character).toNat ∧
        (utf8FirstByte character).toNat ≤ upper) ↔
      (lower ≤ character.toNat ∧ character.toNat ≤ upper) := by
  by_cases ascii : character.toNat ≤ 127
  · rw [utf8FirstByte_toNat_of_ascii character ascii]
  · have encodedLarge :=
      utf8FirstByte_toNat_gt_ascii character ascii
    omega

private theorem utf8FirstByte_eq_ascii_iff
    (character : Char)
    (ascii : UInt8)
    (asciiBound : ascii.toNat ≤ 127) :
    utf8FirstByte character = ascii ↔
      character.toNat = ascii.toNat := by
  constructor
  · intro byteEquation
    by_cases characterAscii : character.toNat ≤ 127
    · calc
        character.toNat = (utf8FirstByte character).toNat :=
          (utf8FirstByte_toNat_of_ascii character characterAscii).symm
        _ = ascii.toNat := congrArg UInt8.toNat byteEquation
    · have encodedLarge :=
        utf8FirstByte_toNat_gt_ascii character characterAscii
      rw [byteEquation] at encodedLarge
      omega
  · intro valueEquation
    have characterAscii : character.toNat ≤ 127 := by
      omega
    apply UInt8.toNat_inj.mp
    rw [utf8FirstByte_toNat_of_ascii character characterAscii,
      valueEquation]

private theorem isAsciiLowerByte_firstByte
    (character : Char) :
    isAsciiLowerByte (utf8FirstByte character) =
      isAsciiLower character := by
  apply Bool.eq_iff_iff.mpr
  simp only [isAsciiLowerByte, isAsciiLower, Bool.and_eq_true,
    decide_eq_true_eq, UInt8.le_iff_toNat_le, Char.le_def,
    UInt32.le_iff_toNat_le]
  simpa using
    utf8FirstByte_range_iff character 97 122 (by decide)

private theorem isAsciiUpperByte_firstByte
    (character : Char) :
    isAsciiUpperByte (utf8FirstByte character) =
      isAsciiUpper character := by
  apply Bool.eq_iff_iff.mpr
  simp only [isAsciiUpperByte, isAsciiUpper, Bool.and_eq_true,
    decide_eq_true_eq, UInt8.le_iff_toNat_le, Char.le_def,
    UInt32.le_iff_toNat_le]
  simpa using
    utf8FirstByte_range_iff character 65 90 (by decide)

private theorem isAsciiDigitByte_firstByte
    (character : Char) :
    isAsciiDigitByte (utf8FirstByte character) =
      isAsciiDigit character := by
  apply Bool.eq_iff_iff.mpr
  simp only [isAsciiDigitByte, isAsciiDigit, Bool.and_eq_true,
    decide_eq_true_eq, UInt8.le_iff_toNat_le, Char.le_def,
    UInt32.le_iff_toNat_le]
  simpa using
    utf8FirstByte_range_iff character 48 57 (by decide)

private theorem isAsciiHexDigitByte_firstByte
    (character : Char) :
    isAsciiHexDigitByte (utf8FirstByte character) =
      isAsciiHexDigit character := by
  apply Bool.eq_iff_iff.mpr
  simp only [isAsciiHexDigitByte, isAsciiHexDigit, isAsciiDigitByte,
    isAsciiDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    UInt8.le_iff_toNat_le, Char.le_def, UInt32.le_iff_toNat_le]
  have decimal :=
    utf8FirstByte_range_iff character 48 57 (by decide)
  have lower :=
    utf8FirstByte_range_iff character 97 102 (by decide)
  have upper :=
    utf8FirstByte_range_iff character 65 70 (by decide)
  simpa using or_congr (or_congr decimal lower) upper

private theorem utf8FirstByte_eq_underscore_iff
    (character : Char) :
    utf8FirstByte character = 95 ↔ character = '_' := by
  calc
    utf8FirstByte character = 95 ↔
        character.toNat = (95 : UInt8).toNat :=
      utf8FirstByte_eq_ascii_iff character 95 (by decide)
    _ ↔ character.toNat = '_'.toNat := Iff.rfl
    _ ↔ character = '_' := Char.toNat_inj

private theorem utf8FirstByte_eq_slash_iff
    (character : Char) :
    utf8FirstByte character = 47 ↔ character = '/' := by
  calc
    utf8FirstByte character = 47 ↔
        character.toNat = (47 : UInt8).toNat :=
      utf8FirstByte_eq_ascii_iff character 47 (by decide)
    _ ↔ character.toNat = '/'.toNat := Iff.rfl
    _ ↔ character = '/' := Char.toNat_inj

private theorem utf8FirstByte_eq_star_iff
    (character : Char) :
    utf8FirstByte character = 42 ↔ character = '*' := by
  calc
    utf8FirstByte character = 42 ↔
        character.toNat = (42 : UInt8).toNat :=
      utf8FirstByte_eq_ascii_iff character 42 (by decide)
    _ ↔ character.toNat = '*'.toNat := Iff.rfl
    _ ↔ character = '*' := Char.toNat_inj

private theorem utf8FirstByte_eq_x_iff
    (character : Char) :
    utf8FirstByte character = 120 ↔ character = 'x' := by
  calc
    utf8FirstByte character = 120 ↔
        character.toNat = (120 : UInt8).toNat :=
      utf8FirstByte_eq_ascii_iff character 120 (by decide)
    _ ↔ character.toNat = 'x'.toNat := Iff.rfl
    _ ↔ character = 'x' := Char.toNat_inj

private theorem isIdentifierContinueByte_firstByte
    (character : Char) :
    isIdentifierContinueByte (utf8FirstByte character) =
      isIdentifierContinue character := by
  apply Bool.eq_iff_iff.mpr
  simp only [isIdentifierContinueByte, isIdentifierContinue,
    isIdentifierStart, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    isAsciiLowerByte_firstByte, isAsciiUpperByte_firstByte,
    isAsciiDigitByte_firstByte]
  exact or_congr (or_congr (Iff.rfl) (Iff.rfl))
    (utf8FirstByte_eq_underscore_iff character)

private theorem whitespaceAlternatives
    (character : Char)
    (whitespace : isWhitespace character = true) :
    character = ' ' ∨ character = '\t' ∨ character = '\r' ∨
      character = '\n' ∨ character.toNat = 12 := by
  simpa [isWhitespace, or_assoc] using whitespace

private theorem isWhitespace_utf8Size
    (character : Char)
    (whitespace : isWhitespace character = true) :
    character.utf8Size = 1 := by
  apply Char.utf8Size_eq_one_iff.mpr
  apply UInt32.le_iff_toNat_le.mpr
  rcases whitespaceAlternatives character whitespace with
    rfl | rfl | rfl | rfl | formFeed
  · decide
  · decide
  · decide
  · decide
  · change character.val.toNat = 12 at formFeed
    rw [show (127 : UInt32).toNat = 127 by decide]
    omega

private theorem isWhitespace_firstByte
    (character : Char)
    (whitespace : isWhitespace character = true) :
    Lexed.IsAsciiWhitespaceByte (utf8FirstByte character) := by
  rcases whitespaceAlternatives character whitespace with
    rfl | rfl | rfl | rfl | formFeed
  · simp [Lexed.IsAsciiWhitespaceByte, utf8FirstByte]
  · simp [Lexed.IsAsciiWhitespaceByte, utf8FirstByte]
  · simp [Lexed.IsAsciiWhitespaceByte, utf8FirstByte]
  · simp [Lexed.IsAsciiWhitespaceByte, utf8FirstByte]
  · unfold Lexed.IsAsciiWhitespaceByte
    exact Or.inr (Or.inr (Or.inl
      ((utf8FirstByte_eq_ascii_iff character 12 (by decide)).mpr
        (by simpa using formFeed))))

private theorem utf8EncodeChar_getElem?_zero
    (character : Char) :
    (String.utf8EncodeChar character)[0]? =
      some (utf8FirstByte character) := by
  simp only [String.utf8EncodeChar, utf8FirstByte]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

private theorem uint8OfNat_ne_lineFeed_of_range
    (value : Nat)
    (lowerBound : 128 ≤ value)
    (upperBound : value < 256) :
    UInt8.ofNat value ≠ 10 := by
  intro equation
  have values := congrArg UInt8.toNat equation
  change value % 2 ^ 8 = 10 at values
  rw [show 2 ^ 8 = 256 by decide,
    Nat.mod_eq_of_lt upperBound] at values
  omega

private theorem utf8EncodeChar_contains_lineFeed_iff
    (character : Char) :
    (10 : UInt8) ∈ String.utf8EncodeChar character ↔
      character = '\n' := by
  constructor
  · intro contains
    simp only [String.utf8EncodeChar] at contains
    split at contains
    · rename_i ascii
      simp only [List.mem_singleton] at contains
      have values := congrArg UInt8.toNat contains
      change 10 = character.val.toNat % 2 ^ 8 at values
      rw [show 2 ^ 8 = 256 by decide,
        Nat.mod_eq_of_lt (by omega)] at values
      apply Char.toNat_inj.mp
      change character.val.toNat = 10
      omega
    · split at contains
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at contains
        rcases contains with leading | continuation
        · exact False.elim
            (uint8OfNat_ne_lineFeed_of_range
              (character.val.toNat / 64 % 32 + 192)
              (by omega)
              (by
                have bound := Nat.mod_lt
                  (character.val.toNat / 64) (by omega : 0 < 32)
                omega)
              leading.symm)
        · exact False.elim
            (uint8OfNat_ne_lineFeed_of_range
              (character.val.toNat % 64 + 128)
              (by omega)
              (by
                have bound := Nat.mod_lt character.val.toNat
                  (by omega : 0 < 64)
                omega)
              continuation.symm)
      · split at contains
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at contains
          rcases contains with leading | middle | trailing
          · exact False.elim
              (uint8OfNat_ne_lineFeed_of_range
                (character.val.toNat / 4096 % 16 + 224)
                (by omega)
                (by
                  have bound := Nat.mod_lt
                    (character.val.toNat / 4096) (by omega : 0 < 16)
                  omega)
                leading.symm)
          · exact False.elim
              (uint8OfNat_ne_lineFeed_of_range
                (character.val.toNat / 64 % 64 + 128)
                (by omega)
                (by
                  have bound := Nat.mod_lt
                    (character.val.toNat / 64) (by omega : 0 < 64)
                  omega)
                middle.symm)
          · exact False.elim
              (uint8OfNat_ne_lineFeed_of_range
                (character.val.toNat % 64 + 128)
                (by omega)
                (by
                  have bound := Nat.mod_lt character.val.toNat
                    (by omega : 0 < 64)
                  omega)
                trailing.symm)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at contains
          rcases contains with leading | second | third | trailing
          · exact False.elim
              (uint8OfNat_ne_lineFeed_of_range
                (character.val.toNat / 262144 % 8 + 240)
                (by omega)
                (by
                  have bound := Nat.mod_lt
                    (character.val.toNat / 262144) (by omega : 0 < 8)
                  omega)
                leading.symm)
          · exact False.elim
              (uint8OfNat_ne_lineFeed_of_range
                (character.val.toNat / 4096 % 64 + 128)
                (by omega)
                (by
                  have bound := Nat.mod_lt
                    (character.val.toNat / 4096) (by omega : 0 < 64)
                  omega)
                second.symm)
          · exact False.elim
              (uint8OfNat_ne_lineFeed_of_range
                (character.val.toNat / 64 % 64 + 128)
                (by omega)
                (by
                  have bound := Nat.mod_lt
                    (character.val.toNat / 64) (by omega : 0 < 64)
                  omega)
                third.symm)
          · exact False.elim
              (uint8OfNat_ne_lineFeed_of_range
                (character.val.toNat % 64 + 128)
                (by omega)
                (by
                  have bound := Nat.mod_lt character.val.toNat
                    (by omega : 0 < 64)
                  omega)
                trailing.symm)
  · rintro rfl
    decide

private theorem utf8EncodedCharacters_do_not_contain_lineFeed
    (characters : List Char)
    (noLineFeed : characters.all (· != '\n') = true) :
    (10 : UInt8) ∉
      (String.ofList characters).toByteArray.data.toList := by
  induction characters with
  | nil =>
      simp
  | cons character rest inductionHypothesis =>
      rw [List.all_cons, Bool.and_eq_true] at noLineFeed
      have characterNotLineFeed : character ≠ '\n' := by
        simpa using noLineFeed.1
      have characterBytesDoNotContain :
          (10 : UInt8) ∉ String.utf8EncodeChar character := by
        intro contains
        exact characterNotLineFeed
          ((utf8EncodeChar_contains_lineFeed_iff character).mp contains)
      change (10 : UInt8) ∉ (List.utf8Encode (character :: rest)).data.toList
      rw [List.utf8Encode_cons, ByteArray.data_append,
        Array.toList_append, List.mem_append, not_or]
      refine ⟨?_, inductionHypothesis noLineFeed.2⟩
      simpa [List.utf8Encode] using characterBytesDoNotContain

private theorem stringOfList_two_slashes_bytes
    (body : List Char) :
    (String.ofList ('/' :: '/' :: body)).toByteArray.data.toList =
      47 :: 47 ::
        (String.ofList body).toByteArray.data.toList := by
  change (List.utf8Encode ('/' :: '/' :: body)).data.toList = _
  rw [List.utf8Encode_cons, List.utf8Encode_cons,
    ByteArray.data_append, ByteArray.data_append,
    Array.toList_append, Array.toList_append]
  have slashEncoding : String.utf8EncodeChar '/' = [47] := by decide
  simp [List.utf8Encode, slashEncoding]

private theorem stringOfList_slash_star_bytes
    (body : List Char) :
    (String.ofList ('/' :: '*' :: body)).toByteArray.data.toList =
      47 :: 42 ::
        (String.ofList body).toByteArray.data.toList := by
  change (List.utf8Encode ('/' :: '*' :: body)).data.toList = _
  rw [List.utf8Encode_cons, List.utf8Encode_cons,
    ByteArray.data_append, ByteArray.data_append,
    Array.toList_append, Array.toList_append]
  have slashEncoding : String.utf8EncodeChar '/' = [47] := by decide
  have starEncoding : String.utf8EncodeChar '*' = [42] := by decide
  simp [List.utf8Encode, slashEncoding, starEncoding]

private def encodedCharacters (characters : List Char) : List UInt8 :=
  (String.ofList characters).toByteArray.data.toList

private theorem encodedCharacters_cons
    (character : Char)
    (characters : List Char) :
    encodedCharacters (character :: characters) =
      String.utf8EncodeChar character ++ encodedCharacters characters := by
  unfold encodedCharacters
  change (List.utf8Encode (character :: characters)).data.toList = _
  rw [List.utf8Encode_cons, ByteArray.data_append,
    Array.toList_append]
  simp [List.utf8Encode]

private theorem utf8EncodeChar_firstByte
    (character : Char) :
    ∃ trailing,
      String.utf8EncodeChar character =
        utf8FirstByte character :: trailing := by
  simp only [String.utf8EncodeChar, utf8FirstByte]
  split
  · exact ⟨[], rfl⟩
  · split
    · exact ⟨[UInt8.ofNat (character.val.toNat % 64 + 128)], rfl⟩
    · split
      · exact ⟨[
          UInt8.ofNat (character.val.toNat / 64 % 64 + 128),
          UInt8.ofNat (character.val.toNat % 64 + 128)], rfl⟩
      · exact ⟨[
          UInt8.ofNat (character.val.toNat / 4096 % 64 + 128),
          UInt8.ofNat (character.val.toNat / 64 % 64 + 128),
          UInt8.ofNat (character.val.toNat % 64 + 128)], rfl⟩

private theorem uint8OfNat_toNat_gt_ascii_of_range
    (value : Nat)
    (lowerBound : 128 ≤ value)
    (upperBound : value < 256) :
    127 < (UInt8.ofNat value).toNat := by
  change 127 < value % 2 ^ 8
  rw [show 2 ^ 8 = 256 by decide,
    Nat.mod_eq_of_lt upperBound]
  exact lowerBound

private theorem blockBodyValidator_other
    {validates : List UInt8 → Nat → Bool}
    (equation : ∀ bytes depth,
      validates bytes depth =
        match bytes with
        | [] => false
        | 47 :: 42 :: rest => validates rest (depth + 1)
        | 42 :: 47 :: rest =>
            if depth == 1 then rest.isEmpty
            else validates rest (depth - 1)
        | _ :: rest => validates rest depth)
    (byte : UInt8)
    (rest : List UInt8)
    (depth : Nat)
    (notSlash : byte ≠ 47)
    (notStar : byte ≠ 42) :
    validates (byte :: rest) depth = validates rest depth := by
  rw [equation]
  cases rest with
  | nil => simp
  | cons next trailing =>
      simp [notSlash, notStar]

private theorem blockBodyValidator_strip
    {validates : List UInt8 → Nat → Bool}
    (equation : ∀ bytes depth,
      validates bytes depth =
        match bytes with
        | [] => false
        | 47 :: 42 :: rest => validates rest (depth + 1)
        | 42 :: 47 :: rest =>
            if depth == 1 then rest.isEmpty
            else validates rest (depth - 1)
        | _ :: rest => validates rest depth)
    (leading trailing : List UInt8)
    (depth : Nat)
    (notSyntax : ∀ byte ∈ leading, byte ≠ 47 ∧ byte ≠ 42) :
    validates (leading ++ trailing) depth = validates trailing depth := by
  induction leading with
  | nil => rfl
  | cons byte rest inductionHypothesis =>
      rw [List.cons_append,
        blockBodyValidator_other equation byte (rest ++ trailing) depth
          (notSyntax byte (by simp)).1
          (notSyntax byte (by simp)).2]
      exact inductionHypothesis (by
        intro candidate member
        exact notSyntax candidate (by simp [member]))

private theorem utf8EncodeChar_byte_gt_ascii
    (character : Char)
    (notAscii : ¬ character.toNat ≤ 127)
    (byte : UInt8)
    (member : byte ∈ String.utf8EncodeChar character) :
    127 < byte.toNat := by
  change ¬ character.val.toNat ≤ 127 at notAscii
  simp only [String.utf8EncodeChar] at member
  rw [if_neg notAscii] at member
  split at member
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · apply uint8OfNat_toNat_gt_ascii_of_range
      · omega
      · have bound := Nat.mod_lt
          (character.val.toNat / 64) (by omega : 0 < 32)
        omega
    · apply uint8OfNat_toNat_gt_ascii_of_range
      · omega
      · have bound := Nat.mod_lt character.val.toNat
          (by omega : 0 < 64)
        omega
  · split at member
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · apply uint8OfNat_toNat_gt_ascii_of_range
        · omega
        · have bound := Nat.mod_lt
            (character.val.toNat / 4096) (by omega : 0 < 16)
          omega
      · apply uint8OfNat_toNat_gt_ascii_of_range
        · omega
        · have bound := Nat.mod_lt
            (character.val.toNat / 64) (by omega : 0 < 64)
          omega
      · apply uint8OfNat_toNat_gt_ascii_of_range
        · omega
        · have bound := Nat.mod_lt character.val.toNat
            (by omega : 0 < 64)
          omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · apply uint8OfNat_toNat_gt_ascii_of_range
        · omega
        · have bound := Nat.mod_lt
            (character.val.toNat / 262144) (by omega : 0 < 8)
          omega
      · apply uint8OfNat_toNat_gt_ascii_of_range
        · omega
        · have bound := Nat.mod_lt
            (character.val.toNat / 4096) (by omega : 0 < 64)
          omega
      · apply uint8OfNat_toNat_gt_ascii_of_range
        · omega
        · have bound := Nat.mod_lt
            (character.val.toNat / 64) (by omega : 0 < 64)
          omega
      · apply uint8OfNat_toNat_gt_ascii_of_range
        · omega
        · have bound := Nat.mod_lt character.val.toNat
            (by omega : 0 < 64)
          omega

private theorem blockBodyValidator_encoded_other
    {validates : List UInt8 → Nat → Bool}
    (equation : ∀ bytes depth,
      validates bytes depth =
        match bytes with
        | [] => false
        | 47 :: 42 :: rest => validates rest (depth + 1)
        | 42 :: 47 :: rest =>
            if depth == 1 then rest.isEmpty
            else validates rest (depth - 1)
        | _ :: rest => validates rest depth)
    (character : Char)
    (rest : List Char)
    (depth : Nat)
    (notOpen : ∀ trailing,
      character = '/' → rest = '*' :: trailing → False)
    (notClose : ∀ trailing,
      character = '*' → rest = '/' :: trailing → False) :
    validates (encodedCharacters (character :: rest)) depth =
      validates (encodedCharacters rest) depth := by
  rw [encodedCharacters_cons]
  by_cases ascii : character.toNat ≤ 127
  · have encodingEquation :
        String.utf8EncodeChar character = [utf8FirstByte character] := by
      change character.val.toNat ≤ 127 at ascii
      simp only [String.utf8EncodeChar, utf8FirstByte]
      rw [if_pos ascii, if_pos ascii]
    rw [encodingEquation, List.singleton_append]
    by_cases slash : character = '/'
    · subst character
      cases rest with
      | nil =>
          rw [equation]
          rfl
      | cons next trailing =>
          have nextNotStar : next ≠ '*' := by
            intro nextStar
            subst next
            exact notOpen trailing rfl rfl
          obtain ⟨nextBytes, nextEncoding⟩ :=
            utf8EncodeChar_firstByte next
          have firstNotStar : utf8FirstByte next ≠ 42 := by
            intro byteEquation
            exact nextNotStar
              ((utf8FirstByte_eq_star_iff next).mp byteEquation)
          rw [encodedCharacters_cons, nextEncoding,
            List.cons_append]
          rw [equation]
          rw [show utf8FirstByte '/' = 47 by decide]
          simp [firstNotStar]
    · by_cases star : character = '*'
      · subst character
        cases rest with
        | nil =>
            rw [equation]
            rfl
        | cons next trailing =>
            have nextNotSlash : next ≠ '/' := by
              intro nextSlash
              subst next
              exact notClose trailing rfl rfl
            obtain ⟨nextBytes, nextEncoding⟩ :=
              utf8EncodeChar_firstByte next
            have firstNotSlash : utf8FirstByte next ≠ 47 := by
              intro byteEquation
              exact nextNotSlash
                ((utf8FirstByte_eq_slash_iff next).mp byteEquation)
            rw [encodedCharacters_cons, nextEncoding,
              List.cons_append]
            rw [equation]
            rw [show utf8FirstByte '*' = 42 by decide]
            simp [firstNotSlash]
      · exact blockBodyValidator_other equation
          (utf8FirstByte character) (encodedCharacters rest) depth
          (by
            intro byteEquation
            exact slash
              ((utf8FirstByte_eq_slash_iff character).mp byteEquation))
          (by
            intro byteEquation
            exact star
              ((utf8FirstByte_eq_star_iff character).mp byteEquation))
  · apply blockBodyValidator_strip equation
    intro byte member
    have byteLarge := utf8EncodeChar_byte_gt_ascii
      character ascii byte member
    constructor
    · intro byteEquation
      have values := congrArg UInt8.toNat byteEquation
      rw [show (47 : UInt8).toNat = 47 by decide] at values
      omega
    · intro byteEquation
      have values := congrArg UInt8.toNat byteEquation
      rw [show (42 : UInt8).toNat = 42 by decide] at values
      omega

private def takeWhile (predicate : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | character :: rest =>
      if predicate character then
        let (taken, remaining) := takeWhile predicate rest
        (character :: taken, remaining)
      else
        ([], character :: rest)

private theorem takeWhile_remainder_length_le
    (predicate : Char → Bool)
    (characters : List Char) :
    (takeWhile predicate characters).2.length ≤ characters.length := by
  induction characters with
  | nil =>
      simp [takeWhile]
  | cons character rest inductionHypothesis =>
      simp only [takeWhile]
      split
      · exact Nat.le_trans inductionHypothesis (Nat.le_succ _)
      · simp

private theorem takeWhile_partition
    (predicate : Char → Bool)
    (characters : List Char) :
    (takeWhile predicate characters).1 ++
        (takeWhile predicate characters).2 = characters := by
  induction characters with
  | nil =>
      simp [takeWhile]
  | cons character rest inductionHypothesis =>
      simp only [takeWhile]
      split
      · simp only [List.cons_append, List.cons.injEq, true_and]
        exact inductionHypothesis
      · simp

private theorem takeWhile_taken_all
    (predicate : Char → Bool)
    (characters : List Char) :
    (takeWhile predicate characters).1.all predicate = true := by
  induction characters with
  | nil =>
      simp [takeWhile]
  | cons character rest inductionHypothesis =>
      simp only [takeWhile]
      split
      · simp_all
      · simp

private theorem takeWhile_remainder_stopped
    (predicate : Char → Bool)
    (characters : List Char) :
    ∀ character rest,
      (takeWhile predicate characters).2 = character :: rest →
        predicate character = false := by
  induction characters with
  | nil =>
      simp [takeWhile]
  | cons character rest inductionHypothesis =>
      simp only [takeWhile]
      split
      · exact inductionHypothesis
      · rename_i predicateFalse
        intro next trailing remainderEquation
        cases remainderEquation
        exact Bool.eq_false_iff.mpr predicateFalse

private def classifyIdentifier (text : String) : TokenKind :=
  match text with
  | "function" => .keywordFunction
  | "let" => .keywordLet
  | "if" => .keywordIf
  | "else" => .keywordElse
  | "return" => .keywordReturn
  | _ => .identifier text

private def implementationIsHardKeyword (text : String) : Bool :=
  text == "function" ||
    text == "let" ||
    text == "if" ||
    text == "else" ||
    text == "return"

private def implementationIsIdentifierText (text : String) : Bool :=
  match text.toList with
  | [] => false
  | first :: rest =>
      isIdentifierStart first && rest.all isIdentifierContinue

private def implementationIsCanonical : TokenKind → Bool
  | .identifier text =>
      implementationIsIdentifierText text &&
        !implementationIsHardKeyword text
  | .decimal digits =>
      !digits.isEmpty && digits.toList.all isAsciiDigit
  | .hexadecimal digits =>
      !digits.isEmpty && digits.toList.all isAsciiHexDigit
  | _ => true

private def IdentifierShaped : TokenKind → Prop
  | .keywordFunction
  | .keywordLet
  | .keywordIf
  | .keywordElse
  | .keywordReturn
  | .identifier _ => True
  | _ => False

private theorem classifyIdentifier_identifierShaped
    (text : String) :
    IdentifierShaped (classifyIdentifier text) := by
  unfold classifyIdentifier
  split <;> simp [IdentifierShaped]

private theorem classifyIdentifier_text
    (text : String) :
    (classifyIdentifier text).text = text := by
  unfold classifyIdentifier
  split <;> simp_all [TokenKind.text]

private theorem classifyIdentifier_implementationCanonical
    (first : Char)
    (tail : List Char)
    (firstStarts : isIdentifierStart first = true)
    (tailContinues : tail.all isIdentifierContinue = true) :
    implementationIsCanonical
      (classifyIdentifier (String.ofList (first :: tail))) = true := by
  unfold classifyIdentifier
  split <;>
    simp_all [implementationIsCanonical, implementationIsIdentifierText,
      implementationIsHardKeyword]

private theorem decimal_implementationCanonical
    (first : Char)
    (tail : List Char)
    (firstDigit : isAsciiDigit first = true)
    (tailDigits : tail.all isAsciiDigit = true) :
    implementationIsCanonical
      (.decimal (String.ofList (first :: tail))) = true := by
  simp [implementationIsCanonical, firstDigit, tailDigits]

private theorem hexadecimal_implementationCanonical
    (first : Char)
    (tail : List Char)
    (firstDigit : isAsciiHexDigit first = true)
    (tailDigits : tail.all isAsciiHexDigit = true) :
    implementationIsCanonical
      (.hexadecimal (String.ofList (first :: tail))) = true := by
  simp [implementationIsCanonical, firstDigit, tailDigits]

private theorem implementationIsCanonical_eq_isCanonical
    (kind : TokenKind) :
    implementationIsCanonical kind = kind.isCanonical := by
  have identifierContinueEquation :
      isIdentifierContinue = fun character =>
        ((('a' ≤ character && character ≤ 'z') ||
          ('A' ≤ character && character ≤ 'Z')) ||
          ('0' ≤ character && character ≤ '9') ||
          character = '_') := by
    funext character
    rfl
  have identifierStartEquation :
      isIdentifierStart = fun character =>
        ('a' ≤ character && character ≤ 'z') ||
          ('A' ≤ character && character ≤ 'Z') := by
    rfl
  have decimalDigitEquation :
      isAsciiDigit = fun character =>
        '0' ≤ character && character ≤ '9' := by
    rfl
  have hexadecimalDigitEquation :
      isAsciiHexDigit = fun character =>
        ('0' ≤ character && character ≤ '9') ||
          ('a' ≤ character && character ≤ 'f') ||
          ('A' ≤ character && character ≤ 'F') := by
    rfl
  cases kind with
  | identifier value =>
      rw [TokenKind.identifier_isCanonical_equation]
      simp only [implementationIsCanonical,
        implementationIsIdentifierText, implementationIsHardKeyword]
      rw [identifierStartEquation, identifierContinueEquation]
      rfl
  | decimal digits =>
      rw [TokenKind.decimal_isCanonical_equation]
      simp only [implementationIsCanonical]
      rw [decimalDigitEquation]
  | hexadecimal digits =>
      rw [TokenKind.hexadecimal_isCanonical_equation]
      simp only [implementationIsCanonical]
      rw [hexadecimalDigitEquation]
  | keywordFunction | keywordLet | keywordIf | keywordElse |
    keywordReturn | arrow | equal | equalEqual | bang | bangEqual |
    less | lessEqual | greater | greaterEqual | plus | minus | star |
    slash | percent | ampersand | caret | pipe | leftParen |
    rightParen | leftBrace | rightBrace | colon | semicolon | comma =>
      rfl

private theorem canonical_of_implementation
    {kind : TokenKind}
    (canonical : implementationIsCanonical kind = true) :
    kind.Canonical := by
  unfold TokenKind.Canonical
  rw [← implementationIsCanonical_eq_isCanonical]
  exact canonical

private def token
    (file : SourceFile)
    (kind : TokenKind)
    (startByte endByte : Nat) : Token := {
  kind
  span := sourceSpan file startByte endByte
}

private def invalidCharacter
    (file : SourceFile)
    (offset : Nat)
    (character : Char) : LexError := {
  code := "SL0001"
  span := sourceSpan file offset (offset + character.utf8Size)
  kind := .invalidCharacter character
}

private def skipBlockComment
    (file : SourceFile)
    (commentStart : Nat) :
    List Char → Nat → Nat → Except LexError (List Char × Nat)
  | [], _, currentByte =>
      .error {
        code := "SL0002"
        span := sourceSpan file commentStart currentByte
        kind := .unterminatedBlockComment
      }
  | '/' :: '*' :: rest, depth, currentByte =>
      skipBlockComment file commentStart rest (depth + 1) (currentByte + 2)
  | '*' :: '/' :: rest, depth, currentByte =>
      if depth == 1 then
        .ok (rest, currentByte + 2)
      else
        skipBlockComment file commentStart rest (depth - 1) (currentByte + 2)
  | character :: rest, depth, currentByte =>
      skipBlockComment file commentStart rest depth (currentByte + character.utf8Size)

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

private def blockCommentBodyValid : List Char → Nat → Bool
  | [], _ => false
  | '/' :: '*' :: rest, depth =>
      blockCommentBodyValid rest (depth + 1)
  | '*' :: '/' :: rest, depth =>
      if depth == 1 then rest.isEmpty
      else blockCommentBodyValid rest (depth - 1)
  | _ :: rest, depth =>
      blockCommentBodyValid rest depth

private theorem blockCommentBodyValid_to_validator
    {validates : List UInt8 → Nat → Bool}
    (equation : ∀ bytes depth,
      validates bytes depth =
        match bytes with
        | [] => false
        | 47 :: 42 :: rest => validates rest (depth + 1)
        | 42 :: 47 :: rest =>
            if depth == 1 then rest.isEmpty
            else validates rest (depth - 1)
        | _ :: rest => validates rest depth)
    (characters : List Char)
    (depth : Nat)
    (valid : blockCommentBodyValid characters depth = true) :
    validates (encodedCharacters characters) depth = true := by
  induction characters, depth using blockCommentBodyValid.induct with
  | case1 depth =>
      simp [blockCommentBodyValid] at valid
  | case2 rest depth inductionHypothesis =>
      have recursiveValid :
          blockCommentBodyValid rest (depth + 1) = true := by
        simpa [blockCommentBodyValid] using valid
      have slashEncoding : String.utf8EncodeChar '/' = [47] := by decide
      have starEncoding : String.utf8EncodeChar '*' = [42] := by decide
      rw [encodedCharacters_cons, encodedCharacters_cons,
        slashEncoding, starEncoding]
      simp only [List.singleton_append]
      rw [equation]
      exact inductionHypothesis recursiveValid
  | case3 rest depth depthIsOne =>
      have restEmpty : rest = [] := by
        have validEmpty : rest.isEmpty = true := by
          simpa [blockCommentBodyValid, depthIsOne] using valid
        simpa [List.isEmpty_iff] using validEmpty
      subst rest
      have starEncoding : String.utf8EncodeChar '*' = [42] := by decide
      have slashEncoding : String.utf8EncodeChar '/' = [47] := by decide
      rw [encodedCharacters_cons, encodedCharacters_cons,
        starEncoding, slashEncoding]
      simp only [List.singleton_append]
      rw [equation]
      simp [depthIsOne, encodedCharacters]
  | case4 rest depth depthIsNotOne inductionHypothesis =>
      have recursiveValid :
          blockCommentBodyValid rest (depth - 1) = true := by
        simpa [blockCommentBodyValid, depthIsNotOne] using valid
      have starEncoding : String.utf8EncodeChar '*' = [42] := by decide
      have slashEncoding : String.utf8EncodeChar '/' = [47] := by decide
      rw [encodedCharacters_cons, encodedCharacters_cons,
        starEncoding, slashEncoding]
      simp only [List.singleton_append]
      rw [equation]
      simp only [depthIsNotOne]
      exact inductionHypothesis recursiveValid
  | case5 character rest depth notOpen notClose inductionHypothesis =>
      rw [blockBodyValidator_encoded_other equation character rest depth
        notOpen notClose]
      exact inductionHypothesis (by
        simpa [blockCommentBodyValid, notOpen, notClose] using valid)

private theorem blockCommentCloses_agrees
    {closes : List Char → Nat → Bool}
    (equation : ∀ characters depth,
      closes characters depth =
        match characters with
        | [] => false
        | '/' :: '*' :: rest => closes rest (depth + 1)
        | '*' :: '/' :: rest =>
            if depth == 1 then true else closes rest (depth - 1)
        | _ :: rest => closes rest depth)
    (characters : List Char)
    (depth : Nat) :
    closes characters depth = blockCommentCloses characters depth := by
  induction characters, depth using blockCommentCloses.induct with
  | case1 depth =>
      rw [equation]
      rfl
  | case2 rest depth inductionHypothesis =>
      rw [equation]
      simp only [blockCommentCloses]
      exact inductionHypothesis
  | case3 rest depth depthIsOne =>
      rw [equation]
      simp [blockCommentCloses, depthIsOne]
  | case4 rest depth depthIsNotOne inductionHypothesis =>
      rw [equation]
      simp [blockCommentCloses, depthIsNotOne]
      exact inductionHypothesis
  | case5 character rest depth notOpen notClose inductionHypothesis =>
      rw [equation]
      simp [blockCommentCloses]
      exact inductionHypothesis

private theorem skipBlockComment_success_consumed
    (file : SourceFile)
    (commentStart : Nat)
    (characters remaining : List Char)
    (depth currentByte endByte : Nat)
    (success :
      skipBlockComment file commentStart characters depth currentByte =
        .ok (remaining, endByte)) :
    ∃ consumed,
      characters = consumed ++ remaining ∧
        endByte = currentByte + charactersByteSize consumed := by
  induction characters, depth, currentByte using skipBlockComment.induct
      generalizing remaining endByte with
  | case1 =>
      simp [skipBlockComment] at success
  | case2 rest depth currentByte inductionHypothesis =>
      simp only [skipBlockComment] at success
      obtain ⟨consumed, decomposition, endByteEquation⟩ :=
        inductionHypothesis remaining endByte success
      refine ⟨'/' :: '*' :: consumed, ?_, ?_⟩
      · simp [decomposition]
      · have slashSize : '/'.utf8Size = 1 := by decide
        have starSize : '*'.utf8Size = 1 := by decide
        simp only [charactersByteSize_cons, slashSize, starSize] at *
        omega

  | case3 rest depth currentByte depthIsOne =>
      simp [skipBlockComment, depthIsOne] at success
      obtain ⟨decomposition, endByteEquation⟩ := success
      refine ⟨['*', '/'], by simpa using decomposition, ?_⟩
      have consumedSize : charactersByteSize ['*', '/'] = 2 := by decide
      rw [consumedSize]
      omega
  | case4 rest depth currentByte depthIsNotOne inductionHypothesis =>
      simp [skipBlockComment, depthIsNotOne] at success
      obtain ⟨consumed, decomposition, endByteEquation⟩ :=
        inductionHypothesis remaining endByte success
      refine ⟨'*' :: '/' :: consumed, ?_, ?_⟩
      · simp [decomposition]
      · have starSize : '*'.utf8Size = 1 := by decide
        have slashSize : '/'.utf8Size = 1 := by decide
        simp only [charactersByteSize_cons, starSize, slashSize] at *
        omega
  | case5 character rest depth currentByte notOpen notClose
      inductionHypothesis =>
      simp only [skipBlockComment] at success
      obtain ⟨consumed, decomposition, endByteEquation⟩ :=
        inductionHypothesis remaining endByte success
      refine ⟨character :: consumed, ?_, ?_⟩
      · simp [decomposition]
      · simp only [charactersByteSize_cons] at *
        omega

private theorem skipBlockComment_success_body_valid
    (file : SourceFile)
    (commentStart : Nat)
    (characters remaining : List Char)
    (depth currentByte endByte : Nat)
    (success :
      skipBlockComment file commentStart characters depth currentByte =
        .ok (remaining, endByte)) :
    ∃ consumed,
      characters = consumed ++ remaining ∧
        blockCommentBodyValid consumed depth = true := by
  induction characters, depth, currentByte using skipBlockComment.induct
      generalizing remaining endByte with
  | case1 =>
      simp [skipBlockComment] at success
  | case2 rest depth currentByte inductionHypothesis =>
      simp only [skipBlockComment] at success
      obtain ⟨consumed, decomposition, valid⟩ :=
        inductionHypothesis remaining endByte success
      exact ⟨'/' :: '*' :: consumed, by simp [decomposition], by
        simpa [blockCommentBodyValid] using valid⟩
  | case3 rest depth currentByte depthIsOne =>
      simp [skipBlockComment, depthIsOne] at success
      exact ⟨['*', '/'], by simpa using success.1, by
        simp [blockCommentBodyValid, depthIsOne]⟩
  | case4 rest depth currentByte depthIsNotOne inductionHypothesis =>
      simp [skipBlockComment, depthIsNotOne] at success
      obtain ⟨consumed, decomposition, valid⟩ :=
        inductionHypothesis remaining endByte success
      exact ⟨'*' :: '/' :: consumed, by simp [decomposition], by
        simpa [blockCommentBodyValid, depthIsNotOne] using valid⟩
  | case5 character rest depth currentByte notOpen notClose
      inductionHypothesis =>
      simp only [skipBlockComment] at success
      obtain ⟨consumed, decomposition, valid⟩ :=
        inductionHypothesis remaining endByte success
      cases consumed with
      | nil =>
          simp [blockCommentBodyValid] at valid
      | cons next trailing =>
          have notOpenPrefix :
              ¬ (character = '/' ∧ next = '*') := by
            rintro ⟨rfl, rfl⟩
            apply notOpen (trailing ++ remaining) rfl
            simpa using decomposition
          have notClosePrefix :
              ¬ (character = '*' ∧ next = '/') := by
            rintro ⟨rfl, rfl⟩
            apply notClose (trailing ++ remaining) rfl
            simpa using decomposition
          refine ⟨character :: next :: trailing, by
            simp [decomposition], ?_⟩
          cases character <;> simp_all [blockCommentBodyValid]

private theorem skipBlockComment_failure
    (file : SourceFile)
    (commentStart : Nat)
    (characters : List Char)
    (depth currentByte : Nat)
    (error : LexError)
    (failure :
      skipBlockComment file commentStart characters depth currentByte =
        .error error) :
    error = {
      code := "SL0002"
      span := sourceSpan file commentStart
        (currentByte + charactersByteSize characters)
      kind := .unterminatedBlockComment
    } ∧ blockCommentCloses characters depth = false := by
  induction characters, depth, currentByte using skipBlockComment.induct
      generalizing error with
  | case1 depth currentByte =>
      simp [skipBlockComment] at failure
      cases failure
      simp [blockCommentCloses, charactersByteSize]
  | case2 rest depth currentByte inductionHypothesis =>
      simp only [skipBlockComment] at failure
      obtain ⟨errorEquation, doesNotClose⟩ :=
        inductionHypothesis error failure
      constructor
      · rw [errorEquation]
        have slashSize : '/'.utf8Size = 1 := by decide
        have starSize : '*'.utf8Size = 1 := by decide
        have byteEquation :
            currentByte + 2 + charactersByteSize rest =
              currentByte + charactersByteSize ('/' :: '*' :: rest) := by
          simp only [charactersByteSize_cons, slashSize, starSize]
          omega
        rw [byteEquation]
      · simpa [blockCommentCloses] using doesNotClose
  | case3 rest depth currentByte depthIsOne =>
      simp [skipBlockComment, depthIsOne] at failure
  | case4 rest depth currentByte depthIsNotOne inductionHypothesis =>
      simp [skipBlockComment, depthIsNotOne] at failure
      obtain ⟨errorEquation, doesNotClose⟩ :=
        inductionHypothesis error failure
      constructor
      · rw [errorEquation]
        have starSize : '*'.utf8Size = 1 := by decide
        have slashSize : '/'.utf8Size = 1 := by decide
        have byteEquation :
            currentByte + 2 + charactersByteSize rest =
              currentByte + charactersByteSize ('*' :: '/' :: rest) := by
          simp only [charactersByteSize_cons, starSize, slashSize]
          omega
        rw [byteEquation]
      · simpa [blockCommentCloses, depthIsNotOne] using doesNotClose
  | case5 character rest depth currentByte notOpen notClose
      inductionHypothesis =>
      simp only [skipBlockComment] at failure
      obtain ⟨errorEquation, doesNotClose⟩ :=
        inductionHypothesis error failure
      constructor
      · rw [errorEquation]
        have byteEquation :
            currentByte + character.utf8Size +
                charactersByteSize rest =
              currentByte + charactersByteSize (character :: rest) := by
          simp only [charactersByteSize_cons]
          omega
        rw [byteEquation]
      · simpa [blockCommentCloses, notOpen, notClose] using doesNotClose

private theorem skipBlockComment_remainder_length_le
    (file : SourceFile)
    (commentStart : Nat)
    (characters remaining : List Char)
    (depth currentByte endByte : Nat)
    (success :
      skipBlockComment file commentStart characters depth currentByte =
        .ok (remaining, endByte)) :
    remaining.length ≤ characters.length := by
  induction characters, depth, currentByte using skipBlockComment.induct
      generalizing remaining endByte with
  | case1 =>
      simp [skipBlockComment] at success
  | case2 rest depth currentByte inductionHypothesis =>
      simp only [skipBlockComment] at success
      exact Nat.le_trans
        (inductionHypothesis remaining endByte success) (by
          simp only [List.length_cons]
          omega)
  | case3 rest depth currentByte depthIsOne =>
      simp [skipBlockComment, depthIsOne] at success
      rw [← success.1]
      simp only [List.length_cons]
      omega
  | case4 rest depth currentByte depthIsNotOne inductionHypothesis =>
      simp [skipBlockComment, depthIsNotOne] at success
      exact Nat.le_trans
        (inductionHypothesis remaining endByte success) (by
          simp only [List.length_cons]
          omega)
  | case5 character rest depth currentByte notOpen notClose
      inductionHypothesis =>
      simp only [skipBlockComment] at success
      exact Nat.le_trans
        (inductionHypothesis remaining endByte success) (by simp)

/--
The cursor movement performed by one successful lexer iteration. A source
rejection and end of input have no successor cursor.
-/
def cursorStep
    (file : SourceFile)
    (characters : List Char)
    (offset : Nat) : Option (List Char × Nat) :=
  match characters with
  | [] => none
  | '/' :: '/' :: rest =>
      let (body, remaining) := takeWhile (· != '\n') rest
      some (remaining, offset + 2 + charactersByteSize body)
  | '/' :: '*' :: rest =>
      match skipBlockComment file offset rest 1 (offset + 2) with
      | .error _ => none
      | .ok (remaining, endByte) => some (remaining, endByte)
  | '0' :: 'x' :: first :: rest =>
      if isAsciiHexDigit first then
        let (tail, remaining) := takeWhile isAsciiHexDigit rest
        some (remaining,
          offset + 2 + charactersByteSize (first :: tail))
      else
        some ('x' :: first :: rest, offset + 1)
  | character :: rest =>
      if isWhitespace character then
        some (rest, offset + character.utf8Size)
      else if isIdentifierStart character then
        let (tail, remaining) := takeWhile isIdentifierContinue rest
        some (remaining,
          offset + charactersByteSize (character :: tail))
      else if isAsciiDigit character then
        let (tail, remaining) := takeWhile isAsciiDigit rest
        some (remaining,
          offset + charactersByteSize (character :: tail))
      else
        match character, rest with
        | '-', '>' :: remaining
        | '=', '=' :: remaining
        | '!', '=' :: remaining
        | '<', '=' :: remaining
        | '>', '=' :: remaining =>
            some (remaining, offset + 2)
        | '=', remaining
        | '!', remaining
        | '<', remaining
        | '>', remaining
        | '+', remaining
        | '-', remaining
        | '*', remaining
        | '/', remaining
        | '%', remaining
        | '&', remaining
        | '^', remaining
        | '|', remaining
        | '(', remaining
        | ')', remaining
        | '{', remaining
        | '}', remaining
        | ':', remaining
        | ';', remaining
        | ',', remaining =>
            some (remaining, offset + 1)
        | _, _ => none

private theorem slashCursorStep
    (file : SourceFile)
    (remaining : List Char)
    (offset : Nat)
    (notLineComment : ∀ rest, remaining ≠ '/' :: rest)
    (notBlockComment : ∀ rest, remaining ≠ '*' :: rest) :
    cursorStep file ('/' :: remaining) offset =
      some (remaining, offset + 1) := by
  cases remaining with
  | nil =>
      rfl
  | cons next rest =>
      by_cases nextIsSlash : next = '/'
      · subst next
        exact False.elim (notLineComment rest rfl)
      · by_cases nextIsStar : next = '*'
        · subst next
          exact False.elim (notBlockComment rest rfl)
        · have slashNotWhitespace : isWhitespace '/' = false := by
            decide
          have slashNotIdentifier : isIdentifierStart '/' = false := by
            decide
          have slashNotDigit : isAsciiDigit '/' = false := by
            decide
          simp [cursorStep, nextIsSlash, nextIsStar,
            slashNotWhitespace, slashNotIdentifier, slashNotDigit]

private theorem oneCharacterProgress
    (character : Char)
    (remaining : List Char)
    (offset : Nat) :
    ∃ consumed,
      character :: remaining = consumed ++ remaining ∧
        offset + character.utf8Size =
          offset + charactersByteSize consumed := by
  refine ⟨[character], by simp, ?_⟩
  simp [charactersByteSize]

private theorem oneAsciiCharacterProgress
    (character : Char)
    (remaining : List Char)
    (offset : Nat)
    (ascii : character.utf8Size = 1) :
    ∃ consumed,
      character :: remaining = consumed ++ remaining ∧
        offset + 1 = offset + charactersByteSize consumed := by
  simpa [ascii] using oneCharacterProgress character remaining offset

private theorem twoAsciiCharactersProgress
    (first second : Char)
    (remaining : List Char)
    (offset : Nat)
    (firstAscii : first.utf8Size = 1)
    (secondAscii : second.utf8Size = 1) :
    ∃ consumed,
      first :: second :: remaining = consumed ++ remaining ∧
        offset + 2 = offset + charactersByteSize consumed := by
  refine ⟨[first, second], by simp, ?_⟩
  simp [charactersByteSize, firstAscii, secondAscii]

private theorem cursorStep_progress
    (file : SourceFile)
    (characters remaining : List Char)
    (offset nextOffset : Nat)
    (transition :
      cursorStep file characters offset = some (remaining, nextOffset)) :
    ∃ consumed,
      characters = consumed ++ remaining ∧
        nextOffset = offset + charactersByteSize consumed := by
  unfold cursorStep at transition
  split at transition
  · simp at transition
  · rename_i _ lineRest
    simp only [Option.some.injEq, Prod.mk.injEq] at transition
    obtain ⟨remainingEquation, nextOffsetEquation⟩ := transition
    refine ⟨'/' :: '/' :: (takeWhile (· != '\n') lineRest).1,
      ?_, ?_⟩
    · rw [List.cons_append, List.cons_append,
        ← remainingEquation, takeWhile_partition]
    · have slashSize : '/'.utf8Size = 1 := by decide
      simp only [charactersByteSize_cons, slashSize]
      rw [← nextOffsetEquation]
      omega
  · rename_i _ blockBody
    split at transition
    · simp at transition
    · rename_i blockRemaining blockEnd success
      obtain ⟨consumed, decomposition, byteEquation⟩ :=
        skipBlockComment_success_consumed file offset blockBody
          _ 1 (offset + 2) _ success
      refine ⟨'/' :: '*' :: consumed, ?_, ?_⟩
      · simp_all
      · have slashSize : '/'.utf8Size = 1 := by decide
        have starSize : '*'.utf8Size = 1 := by decide
        simp only [charactersByteSize_cons, slashSize, starSize]
        simp_all
        omega
  · rename_i _ first rest
    split at transition
    · rename_i isHexadecimal
      simp only [Option.some.injEq, Prod.mk.injEq] at transition
      obtain ⟨remainingEquation, nextOffsetEquation⟩ := transition
      refine ⟨'0' :: 'x' :: first ::
          (takeWhile isAsciiHexDigit rest).1, ?_, ?_⟩
      · rw [List.cons_append, List.cons_append, List.cons_append,
          ← remainingEquation, takeWhile_partition]
      · have zeroSize : '0'.utf8Size = 1 := by decide
        have xSize : 'x'.utf8Size = 1 := by decide
        calc
          nextOffset = offset + 2 +
              charactersByteSize
                (first :: (takeWhile isAsciiHexDigit rest).1) :=
            nextOffsetEquation.symm
          _ = offset + charactersByteSize
              ('0' :: 'x' :: first ::
                (takeWhile isAsciiHexDigit rest).1) := by
            simp only [charactersByteSize_cons, zeroSize, xSize]
            omega
    · rename_i isNotHexadecimal
      simp only [Option.some.injEq, Prod.mk.injEq] at transition
      obtain ⟨remainingEquation, nextOffsetEquation⟩ := transition
      refine ⟨['0'], by simp [← remainingEquation], ?_⟩
      have zeroSize : '0'.utf8Size = 1 := by decide
      rw [← nextOffsetEquation]
      simp [charactersByteSize, zeroSize]
  · rename_i _ currentCharacter currentRest _ _ _
    split at transition
    · rename_i whitespace
      simp only [Option.some.injEq, Prod.mk.injEq] at transition
      obtain ⟨remainingEquation, nextOffsetEquation⟩ := transition
      rw [← remainingEquation, ← nextOffsetEquation]
      exact oneCharacterProgress currentCharacter currentRest offset
    · rename_i notWhitespace
      split at transition
      · rename_i identifierStart
        simp only [Option.some.injEq, Prod.mk.injEq] at transition
        obtain ⟨remainingEquation, nextOffsetEquation⟩ := transition
        refine ⟨currentCharacter ::
            (takeWhile isIdentifierContinue currentRest).1,
          ?_, ?_⟩
        · rw [List.cons_append, ← remainingEquation,
            takeWhile_partition]
        · exact nextOffsetEquation.symm
      · rename_i notIdentifierStart
        split at transition
        · rename_i digit
          simp only [Option.some.injEq, Prod.mk.injEq] at transition
          obtain ⟨remainingEquation, nextOffsetEquation⟩ := transition
          refine ⟨currentCharacter ::
              (takeWhile isAsciiDigit currentRest).1,
            ?_, ?_⟩
          · rw [List.cons_append, ← remainingEquation,
              takeWhile_partition]
          · exact nextOffsetEquation.symm
        · rename_i notDigit
          split at transition <;> simp_all
          all_goals obtain ⟨_, nextOffsetEquation⟩ := transition
          all_goals rw [← nextOffsetEquation]
          all_goals first
            | apply twoAsciiCharactersProgress <;> decide
            | apply oneAsciiCharacterProgress <;> decide

/-- The reflexive-transitive implementation trace from the initial cursor. -/
inductive CursorTrace
    (file : SourceFile) : List Char → Nat → Prop where
  | initial : CursorTrace file file.content.toList 0
  | advance
      {characters remaining : List Char}
      {offset nextOffset : Nat}
      (prior : CursorTrace file characters offset)
      (transition :
        cursorStep file characters offset = some (remaining, nextOffset)) :
      CursorTrace file remaining nextOffset

/--
A lexer cursor reached by implementation transitions, together with its exact
consumed source prefix and UTF-8 byte position.
-/
inductive ReachedCursor
    (file : SourceFile)
    (remaining : List Char)
    (offset : Nat) : Prop where
  | intro
      (trace : CursorTrace file remaining offset)
      (consumedPrefix : List Char)
      (sourceDecomposition :
        file.content.toList = consumedPrefix ++ remaining)
      (offsetEquation :
        offset = (String.ofList consumedPrefix).utf8ByteSize) :
      ReachedCursor file remaining offset

namespace ReachedCursor

private theorem byteArray_extract_middle
    (leading payload trailing : ByteArray) :
    (leading ++ payload ++ trailing).extract leading.size
        (leading.size + payload.size) = payload := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [ByteArray.data_extract, Array.toList_extract]
  simp

private theorem byteArray_getElem?_after_prefix
    (leading trailing : ByteArray) :
    (leading ++ trailing).data[leading.size]? = trailing.data[0]? := by
  rw [ByteArray.data_append, Array.getElem?_append,
    ByteArray.size_data]
  rw [if_neg (by omega)]
  simp

private theorem stringOfList_getElem?_zero
    (character : Char)
    (remaining : List Char) :
    (String.ofList (character :: remaining)).toByteArray.data[0]? =
      some (utf8FirstByte character) := by
  change (List.utf8Encode (character :: remaining)).data[0]? = _
  rw [List.utf8Encode_cons, ByteArray.data_append,
    Array.getElem?_append]
  have encodedNonempty : 0 < (List.utf8Encode [character]).size := by
    simp [List.utf8Encode, String.length_utf8EncodeChar,
      character.utf8Size_pos]
  rw [if_pos (by simpa using encodedNonempty)]
  simpa [List.utf8Encode] using
    utf8EncodeChar_getElem?_zero character

private theorem initial (file : SourceFile) :
    ReachedCursor file file.content.toList 0 := by
  refine .intro .initial [] ?_ ?_
  · simp
  · simp

private theorem advance
    {file : SourceFile}
    {characters remaining : List Char}
    {offset nextOffset : Nat}
    (reached : ReachedCursor file characters offset)
    (transition :
      cursorStep file characters offset = some (remaining, nextOffset))
    (consumed : List Char)
    (decomposition : characters = consumed ++ remaining)
    (nextOffsetEquation :
      nextOffset = offset + charactersByteSize consumed) :
    ReachedCursor file remaining nextOffset := by
  cases reached with
  | intro priorTrace priorPrefix sourceEquation offsetEquation =>
      refine .intro (.advance priorTrace transition)
        (priorPrefix ++ consumed) ?_ ?_
      · rw [sourceEquation, decomposition, List.append_assoc]
      · rw [nextOffsetEquation, offsetEquation,
          stringOfListByteSize_eq_charactersByteSize,
          stringOfListByteSize_eq_charactersByteSize,
          charactersByteSize_append]

private theorem advanceFromStep
    {file : SourceFile}
    {characters remaining : List Char}
    {offset nextOffset : Nat}
    (reached : ReachedCursor file characters offset)
    (transition :
      cursorStep file characters offset = some (remaining, nextOffset)) :
    ReachedCursor file remaining nextOffset := by
  obtain ⟨consumed, decomposition, nextOffsetEquation⟩ :=
    cursorStep_progress file characters remaining offset nextOffset transition
  exact reached.advance transition consumed decomposition nextOffsetEquation

private theorem remainingByteSize
    {file : SourceFile}
    {remaining : List Char}
    {offset : Nat}
    (reached : ReachedCursor file remaining offset) :
    file.content.utf8ByteSize =
      offset + charactersByteSize remaining := by
  cases reached with
  | intro _ consumedPrefix sourceEquation offsetEquation =>
      rw [stringByteSize_eq_charactersByteSize, sourceEquation,
        charactersByteSize_append, offsetEquation,
        stringOfListByteSize_eq_charactersByteSize]

private theorem sourceSlice
    {file : SourceFile}
    {characters consumed remaining : List Char}
    {offset : Nat}
    (reached : ReachedCursor file characters offset)
    (decomposition : characters = consumed ++ remaining) :
    file.content.toByteArray.extract offset
        (offset + charactersByteSize consumed) =
      (String.ofList consumed).toByteArray := by
  cases reached with
  | intro _ consumedPrefix sourceEquation offsetEquation =>
      have contentEquation :
          file.content =
            String.ofList consumedPrefix ++
              String.ofList consumed ++ String.ofList remaining := by
        calc
          file.content = String.ofList file.content.toList :=
            String.ofList_toList.symm
          _ = String.ofList
              (consumedPrefix ++ consumed ++ remaining) := by
            rw [sourceEquation, decomposition, List.append_assoc]
          _ = String.ofList consumedPrefix ++
                String.ofList consumed ++ String.ofList remaining := by
            rw [String.ofList_append, String.ofList_append]
      rw [contentEquation, String.toByteArray_append,
        String.toByteArray_append, offsetEquation,
        stringOfListByteSize_eq_charactersByteSize]
      have leadingSize :
          (String.ofList consumedPrefix).toByteArray.size =
            charactersByteSize consumedPrefix := by
        rw [String.size_toByteArray,
          stringOfListByteSize_eq_charactersByteSize]
      have payloadSize :
          (String.ofList consumed).toByteArray.size =
            charactersByteSize consumed := by
        rw [String.size_toByteArray,
          stringOfListByteSize_eq_charactersByteSize]
      have middle := byteArray_extract_middle
          (String.ofList consumedPrefix).toByteArray
          (String.ofList consumed).toByteArray
          (String.ofList remaining).toByteArray
      rw [leadingSize, payloadSize] at middle
      exact middle

private theorem sourceByteAtAfterPrefix
    {file : SourceFile}
    {characters consumed remaining : List Char}
    {offset : Nat}
    (reached : ReachedCursor file characters offset)
    (decomposition : characters = consumed ++ remaining) :
    sourceByteAt file (offset + charactersByteSize consumed) =
      match remaining with
      | [] => none
      | character :: _ => some (utf8FirstByte character) := by
  cases reached with
  | intro _ consumedPrefix sourceEquation offsetEquation =>
      have contentEquation :
          file.content =
            String.ofList consumedPrefix ++
              String.ofList consumed ++ String.ofList remaining := by
        calc
          file.content = String.ofList file.content.toList :=
            String.ofList_toList.symm
          _ = String.ofList
              (consumedPrefix ++ consumed ++ remaining) := by
            rw [sourceEquation, decomposition, List.append_assoc]
          _ = String.ofList consumedPrefix ++
                String.ofList consumed ++ String.ofList remaining := by
            rw [String.ofList_append, String.ofList_append]
      have leadingSize :
          (String.ofList consumedPrefix).toByteArray.size =
            charactersByteSize consumedPrefix := by
        rw [String.size_toByteArray,
          stringOfListByteSize_eq_charactersByteSize]
      have consumedSize :
          (String.ofList consumed).toByteArray.size =
            charactersByteSize consumed := by
        rw [String.size_toByteArray,
          stringOfListByteSize_eq_charactersByteSize]
      have lookup := byteArray_getElem?_after_prefix
        ((String.ofList consumedPrefix).toByteArray ++
          (String.ofList consumed).toByteArray)
        (String.ofList remaining).toByteArray
      rw [ByteArray.size_append, leadingSize, consumedSize] at lookup
      unfold sourceByteAt
      rw [contentEquation, String.toByteArray_append,
        String.toByteArray_append, offsetEquation,
        stringOfListByteSize_eq_charactersByteSize]
      rw [lookup]
      cases remaining with
      | nil =>
          rfl
      | cons character trailing =>
          exact stringOfList_getElem?_zero character trailing

private theorem whitespaceByte
    {file : SourceFile}
    {character : Char}
    {remaining : List Char}
    {offset index : Nat}
    (reached : ReachedCursor file (character :: remaining) offset)
    (whitespace : isWhitespace character = true)
    (indexAtOrAfter : offset ≤ index)
    (indexBefore : index < offset + character.utf8Size) :
    ∃ byte,
      file.content.toByteArray.data[index]? = some byte ∧
        Lexed.IsAsciiWhitespaceByte byte := by
  have characterSize := isWhitespace_utf8Size character whitespace
  have indexEquation : index = offset := by
    rw [characterSize] at indexBefore
    omega
  subst index
  have lookup := reached.sourceByteAtAfterPrefix
    (consumed := []) (remaining := character :: remaining) (by simp)
  refine ⟨utf8FirstByte character, ?_,
    isWhitespace_firstByte character whitespace⟩
  simpa [sourceByteAt, charactersByteSize] using lookup

private theorem noContinuationAfterPrefix
    {file : SourceFile}
    {characters consumed remaining : List Char}
    {offset : Nat}
    (bytePredicate : UInt8 → Bool)
    (characterPredicate : Char → Bool)
    (predicateAgreement : ∀ character,
      bytePredicate (utf8FirstByte character) =
        characterPredicate character)
    (reached : ReachedCursor file characters offset)
    (decomposition : characters = consumed ++ remaining)
    (stopped : ∀ character trailing,
      remaining = character :: trailing →
        characterPredicate character = false) :
    ¬ ∃ byte,
      sourceByteAt file (offset + charactersByteSize consumed) = some byte ∧
        bytePredicate byte = true := by
  intro continues
  rcases continues with ⟨byte, byteAtEquation, accepted⟩
  have lookup := reached.sourceByteAtAfterPrefix decomposition
  cases remaining with
  | nil =>
      simp only at lookup
      rw [lookup] at byteAtEquation
      contradiction
  | cons character trailing =>
      simp only at lookup
      rw [lookup] at byteAtEquation
      cases byteAtEquation
      rw [predicateAgreement character,
        stopped character trailing rfl] at accepted
      contradiction

private theorem byteAfterPrefix_ne_ascii
    {file : SourceFile}
    {characters consumed remaining : List Char}
    {offset : Nat}
    (reached : ReachedCursor file characters offset)
    (decomposition : characters = consumed ++ remaining)
    (targetCharacter : Char)
    (targetByte : UInt8)
    (targetValue : targetCharacter.toNat = targetByte.toNat)
    (targetBound : targetByte.toNat ≤ 127)
    (notHead : ∀ trailing,
      remaining ≠ targetCharacter :: trailing) :
    sourceByteAt file (offset + charactersByteSize consumed) ≠
      some targetByte := by
  intro byteAtEquation
  have lookup := reached.sourceByteAtAfterPrefix decomposition
  cases remaining with
  | nil =>
      simp only at lookup
      rw [lookup] at byteAtEquation
      contradiction
  | cons character trailing =>
      simp only at lookup
      have firstByteEquation :
          utf8FirstByte character = targetByte := by
        exact Option.some.inj (lookup.symm.trans byteAtEquation)
      have characterValue :=
        (utf8FirstByte_eq_ascii_iff character targetByte targetBound).mp
          firstByteEquation
      have characterEquation : character = targetCharacter :=
        Char.toNat_inj.mp (characterValue.trans targetValue.symm)
      subst character
      exact notHead trailing rfl

end ReachedCursor

private theorem identifierDoesNotContinue
    {file : SourceFile}
    {characters consumed remaining : List Char}
    {offset : Nat}
    (reached : ReachedCursor file characters offset)
    (decomposition : characters = consumed ++ remaining)
    (stopped : ∀ character trailing,
      remaining = character :: trailing →
        isIdentifierContinue character = false) :
    ¬ ImplementationIdentifierContinuesAt file
      (offset + charactersByteSize consumed) := by
  exact reached.noContinuationAfterPrefix
    isIdentifierContinueByte isIdentifierContinue
    isIdentifierContinueByte_firstByte decomposition stopped

private theorem decimalDoesNotContinue
    {file : SourceFile}
    {characters consumed remaining : List Char}
    {offset : Nat}
    (reached : ReachedCursor file characters offset)
    (decomposition : characters = consumed ++ remaining)
    (stopped : ∀ character trailing,
      remaining = character :: trailing →
        isAsciiDigit character = false) :
    ¬ ImplementationDecimalContinuesAt file
      (offset + charactersByteSize consumed) := by
  exact reached.noContinuationAfterPrefix
    isAsciiDigitByte isAsciiDigit isAsciiDigitByte_firstByte
    decomposition stopped

private theorem hexadecimalDoesNotContinue
    {file : SourceFile}
    {characters consumed remaining : List Char}
    {offset : Nat}
    (reached : ReachedCursor file characters offset)
    (decomposition : characters = consumed ++ remaining)
    (stopped : ∀ character trailing,
      remaining = character :: trailing →
        isAsciiHexDigit character = false) :
    ¬ ImplementationHexadecimalContinuesAt file
      (offset + charactersByteSize consumed) := by
  exact reached.noContinuationAfterPrefix
    isAsciiHexDigitByte isAsciiHexDigit isAsciiHexDigitByte_firstByte
    decomposition stopped

private theorem decimalZeroIsNotEligible
    {file : SourceFile}
    {rest : List Char}
    {offset : Nat}
    (reached : ReachedCursor file ('0' :: rest) offset)
    (notSpecial : ∀ first trailing,
      '0' :: rest ≠ '0' :: 'x' :: first :: trailing) :
    ¬ ImplementationEligibleHexadecimalAt file offset := by
  intro eligible
  unfold ImplementationEligibleHexadecimalAt at eligible
  have afterZero := reached.sourceByteAtAfterPrefix
    (consumed := ['0']) (remaining := rest) (by simp)
  have zeroSize : charactersByteSize ['0'] = 1 := by decide
  rw [zeroSize] at afterZero
  cases rest with
  | nil =>
      simp only at afterZero
      simp_all
  | cons next trailing =>
      simp only at afterZero
      have nextByte : utf8FirstByte next = 120 := by
        exact Option.some.inj (afterZero.symm.trans eligible.2.1)
      have nextEquation := (utf8FirstByte_eq_x_iff next).mp nextByte
      subst next
      have afterPrefix := reached.sourceByteAtAfterPrefix
        (consumed := ['0', 'x']) (remaining := trailing) (by simp)
      have prefixSize : charactersByteSize ['0', 'x'] = 2 := by decide
      rw [prefixSize] at afterPrefix
      rcases eligible.2.2 with ⟨byte, byteAtEquation, accepted⟩
      cases trailing with
      | nil =>
          simp only at afterPrefix
          simp_all
      | cons first remainder =>
          exact notSpecial first remainder rfl

private theorem implementationIdentifierContinuesAt_iff
    (file : SourceFile)
    (offset : Nat) :
    ImplementationIdentifierContinuesAt file offset ↔
      LexicalGrammar.IdentifierContinuesAt file offset := by
  unfold ImplementationIdentifierContinuesAt
  unfold LexicalGrammar.IdentifierContinuesAt
  simp only [LexicalGrammar.byteAt_equation,
    LexicalGrammar.isIdentifierContinueByte_equation]
  rfl

private theorem implementationDecimalContinuesAt_iff
    (file : SourceFile)
    (offset : Nat) :
    ImplementationDecimalContinuesAt file offset ↔
      LexicalGrammar.DecimalContinuesAt file offset := by
  unfold ImplementationDecimalContinuesAt
  unfold LexicalGrammar.DecimalContinuesAt
  simp only [LexicalGrammar.byteAt_equation,
    LexicalGrammar.isAsciiDigitByte_equation]
  rfl

private theorem implementationHexadecimalContinuesAt_iff
    (file : SourceFile)
    (offset : Nat) :
    ImplementationHexadecimalContinuesAt file offset ↔
      LexicalGrammar.HexadecimalContinuesAt file offset := by
  unfold ImplementationHexadecimalContinuesAt
  unfold LexicalGrammar.HexadecimalContinuesAt
  simp only [LexicalGrammar.byteAt_equation,
    LexicalGrammar.isAsciiHexDigitByte_equation]
  rfl

private theorem implementationEligibleHexadecimalAt_iff
    (file : SourceFile)
    (offset : Nat) :
    ImplementationEligibleHexadecimalAt file offset ↔
      LexicalGrammar.EligibleHexadecimalAt file offset := by
  unfold ImplementationEligibleHexadecimalAt
  unfold LexicalGrammar.EligibleHexadecimalAt
  rw [implementationHexadecimalContinuesAt_iff]
  simp only [LexicalGrammar.byteAt_equation]
  rfl

private theorem identifierShapedImplementationMaximal
    {file : SourceFile}
    {kind : TokenKind}
    {startByte endByte : Nat}
    (shaped : IdentifierShaped kind)
    (stopped :
      ¬ ImplementationIdentifierContinuesAt file endByte) :
    ImplementationTokenMaximalFor
      (token file kind startByte endByte) file := by
  cases kind <;>
    simp_all [IdentifierShaped, ImplementationTokenMaximalFor,
      token, sourceSpan]

private theorem decimalImplementationMaximal
    {file : SourceFile}
    {digits : String}
    {startByte endByte : Nat}
    (stopped : ¬ ImplementationDecimalContinuesAt file endByte)
    (notEligible : digits = "0" →
      ¬ ImplementationEligibleHexadecimalAt file startByte) :
    ImplementationTokenMaximalFor
      (token file (.decimal digits) startByte endByte) file := by
  exact ⟨stopped, notEligible⟩

private theorem hexadecimalImplementationMaximal
    {file : SourceFile}
    {digits : String}
    {startByte endByte : Nat}
    (stopped : ¬ ImplementationHexadecimalContinuesAt file endByte) :
    ImplementationTokenMaximalFor
      (token file (.hexadecimal digits) startByte endByte) file := by
  exact stopped

private theorem implementationTokenMaximalFor_iff
    (value : Token)
    (file : SourceFile) :
    ImplementationTokenMaximalFor value file ↔
      LexicalGrammar.TokenMaximalFor value file := by
  cases value with
  | mk kind span =>
      cases kind <;>
        simp [ImplementationTokenMaximalFor,
          LexicalGrammar.TokenMaximalFor,
          implementationIdentifierContinuesAt_iff,
          implementationDecimalContinuesAt_iff,
          implementationHexadecimalContinuesAt_iff,
          implementationEligibleHexadecimalAt_iff,
          sourceByteAt, LexicalGrammar.byteAt_equation]

private theorem lineCommentBoundary
    {file : SourceFile}
    {rest body remaining : List Char}
    {offset : Nat}
    (reached : ReachedCursor file ('/' :: '/' :: rest) offset)
    (resultEquation :
      takeWhile (· != '\n') rest = (body, remaining)) :
    offset + 2 + charactersByteSize body =
        file.content.toByteArray.size ∨
      file.content.toByteArray.data[
        offset + 2 + charactersByteSize body]? = some 10 := by
  have partition := takeWhile_partition (· != '\n') rest
  rw [resultEquation] at partition
  have sourceDecomposition :
      '/' :: '/' :: rest =
        ('/' :: '/' :: body) ++ remaining := by
    simp [partition]
  have slashSize : '/'.utf8Size = 1 := by decide
  have prefixSize :
      charactersByteSize ('/' :: '/' :: body) =
        2 + charactersByteSize body := by
    simp only [charactersByteSize_cons, slashSize]
    omega
  cases remaining with
  | nil =>
      left
      have sourceSize := reached.remainingByteSize
      rw [sourceDecomposition, charactersByteSize_append,
        prefixSize] at sourceSize
      rw [show charactersByteSize [] = 0 by rfl] at sourceSize
      rw [String.size_toByteArray]
      omega
  | cons character trailing =>
      right
      have remainderEquation :
          (takeWhile (· != '\n') rest).2 =
            character :: trailing := by
        rw [resultEquation]
      have stopped := takeWhile_remainder_stopped
        (· != '\n') rest character trailing remainderEquation
      have characterEquation : character = '\n' := by
        simpa using stopped
      subst character
      have lookup := reached.sourceByteAtAfterPrefix sourceDecomposition
      simp only at lookup
      unfold sourceByteAt at lookup
      rw [prefixSize] at lookup
      simp only [utf8FirstByte] at lookup
      rw [show offset + (2 + charactersByteSize body) =
        offset + 2 + charactersByteSize body by omega] at lookup
      exact lookup

private theorem lineCommentValid
    {file : SourceFile}
    {rest body remaining : List Char}
    {offset : Nat}
    (reached : ReachedCursor file ('/' :: '/' :: rest) offset)
    (resultEquation :
      takeWhile (· != '\n') rest = (body, remaining)) :
    (let endByte := offset + 2 + charactersByteSize body;
      ({
        kind := .line
        span := sourceSpan file offset endByte
      } : Comment).ValidFor file) := by
  dsimp only
  have partition := takeWhile_partition (· != '\n') rest
  rw [resultEquation] at partition
  have sourceDecomposition :
      '/' :: '/' :: rest =
        ('/' :: '/' :: body) ++ remaining := by
    simp [partition]
  have slashSize : '/'.utf8Size = 1 := by decide
  have prefixSize :
      charactersByteSize ('/' :: '/' :: body) =
        2 + charactersByteSize body := by
    simp only [charactersByteSize_cons, slashSize]
    omega
  have sourceSize := reached.remainingByteSize
  rw [sourceDecomposition, charactersByteSize_append,
    prefixSize] at sourceSize
  constructor
  · unfold SourceSpan.ValidFor
    simp only [sourceSpan]
    exact ⟨⟨trivial, by omega⟩, by omega⟩
  · rw [Comment.line_payload_valid_equation]
    simp only [sourceSpan]
    have slice := reached.sourceSlice sourceDecomposition
    rw [prefixSize] at slice
    rw [show offset + (2 + charactersByteSize body) =
      offset + 2 + charactersByteSize body by omega] at slice
    rw [slice]
    rw [stringOfList_two_slashes_bytes]
    rw [Bool.and_eq_true]
    constructor
    · change
        (!(String.ofList body).toByteArray.data.toList.contains 10) = true
      have noLineFeed := utf8EncodedCharacters_do_not_contain_lineFeed
        body (by
          have allTaken := takeWhile_taken_all (· != '\n') rest
          rw [resultEquation] at allTaken
          exact allTaken)
      simpa [List.contains_iff_mem] using noLineFeed
    · rw [Bool.or_eq_true]
      rcases lineCommentBoundary reached resultEquation with
        atEnd | lineFeed
      · exact Or.inl (by simpa using atEnd)
      · exact Or.inr (by simpa using lineFeed)

private theorem blockCommentValid
    {file : SourceFile}
    {rest remaining : List Char}
    {offset endByte : Nat}
    (reached : ReachedCursor file ('/' :: '*' :: rest) offset)
    (success :
      skipBlockComment file offset rest 1 (offset + 2) =
        .ok (remaining, endByte)) :
    ({
      kind := .block
      span := sourceSpan file offset endByte
    } : Comment).ValidFor file := by
  obtain ⟨consumed, bodyDecomposition, bodyValid⟩ :=
    skipBlockComment_success_body_valid file offset rest remaining
      1 (offset + 2) endByte success
  obtain ⟨sizedConsumed, sizeDecomposition, endByteEquation⟩ :=
    skipBlockComment_success_consumed file offset rest remaining
      1 (offset + 2) endByte success
  have consumedEquation : consumed = sizedConsumed := by
    apply List.append_cancel_right
    exact bodyDecomposition.symm.trans sizeDecomposition
  subst sizedConsumed
  have sourceDecomposition :
      '/' :: '*' :: rest =
        ('/' :: '*' :: consumed) ++ remaining := by
    simp [bodyDecomposition]
  have slashSize : '/'.utf8Size = 1 := by decide
  have starSize : '*'.utf8Size = 1 := by decide
  have prefixSize :
      charactersByteSize ('/' :: '*' :: consumed) =
        2 + charactersByteSize consumed := by
    simp only [charactersByteSize_cons, slashSize, starSize]
    omega
  have sourceSize := reached.remainingByteSize
  rw [sourceDecomposition, charactersByteSize_append,
    prefixSize] at sourceSize
  have normalizedEnd :
      endByte = offset + 2 + charactersByteSize consumed := by
    omega
  constructor
  · unfold SourceSpan.ValidFor
    simp only [sourceSpan]
    exact ⟨⟨trivial, by omega⟩, by omega⟩
  · rw [Comment.block_payload_valid_equation]
    simp only [sourceSpan]
    have slice := reached.sourceSlice sourceDecomposition
    rw [prefixSize] at slice
    rw [show offset + (2 + charactersByteSize consumed) =
      offset + 2 + charactersByteSize consumed by omega] at slice
    rw [normalizedEnd, slice, stringOfList_slash_star_bytes]
    apply blockCommentBodyValid_to_validator
      Comment.blockBodyValid_equation consumed 1
    exact bodyValid

private theorem tokenValid_of_spelling
    {file : SourceFile}
    {characters consumed remaining : List Char}
    {offset : Nat}
    (reached : ReachedCursor file characters offset)
    (decomposition : characters = consumed ++ remaining)
    (kind : TokenKind)
    (canonical : kind.Canonical)
    (spelling : kind.text = String.ofList consumed) :
    (token file kind offset
      (offset + charactersByteSize consumed)).ValidFor file := by
  have sourceEndEquation := reached.remainingByteSize
  rw [decomposition, charactersByteSize_append] at sourceEndEquation
  unfold Token.ValidFor
  refine ⟨canonical, ?_, ?_⟩
  · simp [token, sourceSpan, SourceSpan.ValidFor]
    omega
  · have slice := reached.sourceSlice decomposition
    simpa [token, sourceSpan, Token.text, spelling] using slice

private theorem spansOrdered_append_singleton
    (spans : List SourceSpan)
    (next : SourceSpan)
    (ordered : Lexed.SpansOrdered spans)
    (before : ∀ span ∈ spans, span.endByte ≤ next.startByte) :
    Lexed.SpansOrdered (spans ++ [next]) := by
  induction spans with
  | nil =>
      simp [Lexed.SpansOrdered]
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil =>
          simp only [List.cons_append, List.nil_append,
            Lexed.SpansOrdered]
          exact ⟨before first (by simp), trivial⟩
      | cons second trailing =>
          simp only [List.cons_append, Lexed.SpansOrdered] at ordered ⊢
          exact ⟨ordered.1,
            inductionHypothesis ordered.2 (by
              intro span member
              exact before span (List.mem_cons_of_mem first member))⟩

private def PrefixPartitioned
    (file : SourceFile)
    (offset : Nat)
    (tokens : List Token)
    (comments : List Comment) : Prop :=
  ∀ index, index < offset →
    (∃ token ∈ tokens, Lexed.CoversByte token.span index) ∨
    (∃ comment ∈ comments, Lexed.CoversByte comment.span index) ∨
    ∃ byte,
      file.content.toByteArray.data[index]? = some byte ∧
        Lexed.IsAsciiWhitespaceByte byte

private structure AccumulatorInvariant
    (file : SourceFile)
    (offset : Nat)
    (tokens : List Token)
    (comments : List Comment) : Prop where
  tokensSound : ∀ token ∈ tokens,
    token.ValidFor file ∧ LexicalGrammar.TokenMaximalFor token file
  commentsValid : ∀ comment ∈ comments, comment.ValidFor file
  tokensOrdered :
    Lexed.SpansOrdered (tokens.reverse.map (·.span))
  commentsOrdered :
    Lexed.SpansOrdered (comments.reverse.map (·.span))
  crossDisjoint : ∀ token ∈ tokens, ∀ comment ∈ comments,
    Lexed.SpansDisjoint token.span comment.span
  tokensBefore : ∀ token ∈ tokens, token.span.endByte ≤ offset
  commentsBefore : ∀ comment ∈ comments,
    comment.span.endByte ≤ offset
  prefixPartitioned : PrefixPartitioned file offset tokens comments

namespace AccumulatorInvariant

private theorem initial (file : SourceFile) :
    AccumulatorInvariant file 0 [] [] := by
  constructor <;> simp [Lexed.SpansOrdered, PrefixPartitioned]

private theorem addToken
    {file : SourceFile}
    {offset nextOffset : Nat}
    {tokens : List Token}
    {comments : List Comment}
    (invariant : AccumulatorInvariant file offset tokens comments)
    (newToken : Token)
    (valid : newToken.ValidFor file)
    (maximal : LexicalGrammar.TokenMaximalFor newToken file)
    (startEquation : newToken.span.startByte = offset)
    (endEquation : newToken.span.endByte = nextOffset)
    (progress : offset ≤ nextOffset) :
    AccumulatorInvariant file nextOffset (newToken :: tokens) comments := by
  constructor
  · intro candidate member
    rcases List.mem_cons.mp member with rfl | old
    · exact ⟨valid, maximal⟩
    · exact invariant.tokensSound candidate old
  · exact invariant.commentsValid
  · simp only [List.reverse_cons, List.map_append, List.map_singleton]
    apply spansOrdered_append_singleton
    · exact invariant.tokensOrdered
    · intro span member
      rcases List.mem_map.mp member with
        ⟨oldToken, oldMember, spanEquation⟩
      subst span
      rw [startEquation]
      exact invariant.tokensBefore oldToken (by simpa using oldMember)
  · exact invariant.commentsOrdered
  · intro candidate candidateMember comment commentMember
    rcases List.mem_cons.mp candidateMember with rfl | old
    · exact Or.inr (by
        rw [startEquation]
        exact invariant.commentsBefore comment commentMember)
    · exact invariant.crossDisjoint candidate old comment commentMember
  · intro candidate member
    rcases List.mem_cons.mp member with rfl | old
    · rw [endEquation]
      exact Nat.le_refl nextOffset
    · exact Nat.le_trans (invariant.tokensBefore candidate old) progress
  · intro comment member
    exact Nat.le_trans (invariant.commentsBefore comment member) progress
  · intro index indexBefore
    by_cases beforeOld : index < offset
    · rcases invariant.prefixPartitioned index beforeOld with
        token | comment | whitespace
      · rcases token with ⟨oldToken, member, covered⟩
        exact Or.inl ⟨oldToken, by simp [member], covered⟩
      · exact Or.inr (Or.inl comment)
      · exact Or.inr (Or.inr whitespace)
    · exact Or.inl ⟨newToken, by simp, by
        unfold Lexed.CoversByte
        rw [startEquation, endEquation]
        omega⟩

private theorem addComment
    {file : SourceFile}
    {offset nextOffset : Nat}
    {tokens : List Token}
    {comments : List Comment}
    (invariant : AccumulatorInvariant file offset tokens comments)
    (newComment : Comment)
    (valid : newComment.ValidFor file)
    (startEquation : newComment.span.startByte = offset)
    (endEquation : newComment.span.endByte = nextOffset)
    (progress : offset ≤ nextOffset) :
    AccumulatorInvariant file nextOffset tokens (newComment :: comments) := by
  constructor
  · exact invariant.tokensSound
  · intro candidate member
    rcases List.mem_cons.mp member with rfl | old
    · exact valid
    · exact invariant.commentsValid candidate old
  · exact invariant.tokensOrdered
  · simp only [List.reverse_cons, List.map_append, List.map_singleton]
    apply spansOrdered_append_singleton
    · exact invariant.commentsOrdered
    · intro span member
      rcases List.mem_map.mp member with
        ⟨oldComment, oldMember, spanEquation⟩
      subst span
      rw [startEquation]
      exact invariant.commentsBefore oldComment (by simpa using oldMember)
  · intro token tokenMember candidate candidateMember
    rcases List.mem_cons.mp candidateMember with rfl | old
    · exact Or.inl (by
        rw [startEquation]
        exact invariant.tokensBefore token tokenMember)
    · exact invariant.crossDisjoint token tokenMember candidate old
  · intro token member
    exact Nat.le_trans (invariant.tokensBefore token member) progress
  · intro candidate member
    rcases List.mem_cons.mp member with rfl | old
    · rw [endEquation]
      exact Nat.le_refl nextOffset
    · exact Nat.le_trans (invariant.commentsBefore candidate old) progress
  · intro index indexBefore
    by_cases beforeOld : index < offset
    · rcases invariant.prefixPartitioned index beforeOld with
        token | comment | whitespace
      · exact Or.inl token
      · rcases comment with ⟨oldComment, member, covered⟩
        exact Or.inr (Or.inl
          ⟨oldComment, by simp [member], covered⟩)
      · exact Or.inr (Or.inr whitespace)
    · exact Or.inr (Or.inl ⟨newComment, by simp, by
        unfold Lexed.CoversByte
        rw [startEquation, endEquation]
        omega⟩)

private theorem skipWhitespace
    {file : SourceFile}
    {offset nextOffset : Nat}
    {tokens : List Token}
    {comments : List Comment}
    (invariant : AccumulatorInvariant file offset tokens comments)
    (progress : offset ≤ nextOffset)
    (whitespace : ∀ index, offset ≤ index → index < nextOffset →
      ∃ byte,
        file.content.toByteArray.data[index]? = some byte ∧
          Lexed.IsAsciiWhitespaceByte byte) :
    AccumulatorInvariant file nextOffset tokens comments := by
  constructor
  · exact invariant.tokensSound
  · exact invariant.commentsValid
  · exact invariant.tokensOrdered
  · exact invariant.commentsOrdered
  · exact invariant.crossDisjoint
  · intro token member
    exact Nat.le_trans (invariant.tokensBefore token member) progress
  · intro comment member
    exact Nat.le_trans (invariant.commentsBefore comment member) progress
  · intro index indexBefore
    by_cases beforeOld : index < offset
    · exact invariant.prefixPartitioned index beforeOld
    · exact Or.inr (Or.inr
        (whitespace index (by omega) indexBefore))

private theorem lexesAtEnd
    {file : SourceFile}
    {offset : Nat}
    {tokens : List Token}
    {comments : List Comment}
    (reached : ReachedCursor file [] offset)
    (invariant : AccumulatorInvariant file offset tokens comments) :
    LexicalGrammar.Lexes file {
      tokens := tokens.reverse
      comments := comments.reverse
    } := by
  have endEquation : file.content.toByteArray.size = offset := by
    have remainingSize := reached.remainingByteSize
    rw [String.size_toByteArray]
    simpa [charactersByteSize] using remainingSize
  constructor
  · unfold Lexed.ValidFor
    refine ⟨?_, ?_, invariant.tokensOrdered,
      invariant.commentsOrdered, ?_, ?_⟩
    · intro token member
      exact (invariant.tokensSound token (by simpa using member)).1
    · intro comment member
      exact invariant.commentsValid comment (by simpa using member)
    · intro token tokenMember comment commentMember
      exact invariant.crossDisjoint token (by simpa using tokenMember)
        comment (by simpa using commentMember)
    · intro index inBounds
      rcases invariant.prefixPartitioned index (by omega) with
        token | comment | whitespace
      · rcases token with ⟨oldToken, member, covered⟩
        exact Or.inl ⟨oldToken, by simpa using member, covered⟩
      · rcases comment with ⟨oldComment, member, covered⟩
        exact Or.inr (Or.inl
          ⟨oldComment, by simpa using member, covered⟩)
      · exact Or.inr (Or.inr whitespace)
  · intro token member
    exact (invariant.tokensSound token (by simpa using member)).2

end AccumulatorInvariant

private theorem recognizeToken
    {file : SourceFile}
    {characters consumed remaining : List Char}
    {offset : Nat}
    {tokens : List Token}
    {comments : List Comment}
    (reached : ReachedCursor file characters offset)
    (invariant : AccumulatorInvariant file offset tokens comments)
    (decomposition : characters = consumed ++ remaining)
    (kind : TokenKind)
    (canonical : implementationIsCanonical kind = true)
    (spelling : kind.text = String.ofList consumed)
    (maximal : ImplementationTokenMaximalFor
      (token file kind offset
        (offset + charactersByteSize consumed)) file)
    (transition : cursorStep file characters offset =
      some (remaining, offset + charactersByteSize consumed)) :
    ReachedCursor file remaining
        (offset + charactersByteSize consumed) ∧
      AccumulatorInvariant file
        (offset + charactersByteSize consumed)
        (token file kind offset
          (offset + charactersByteSize consumed) :: tokens)
        comments := by
  have valid := tokenValid_of_spelling reached decomposition kind
    (canonical_of_implementation canonical) spelling
  have lexicalMaximal :=
    (implementationTokenMaximalFor_iff
      (token file kind offset
        (offset + charactersByteSize consumed)) file).mp maximal
  exact ⟨reached.advanceFromStep transition,
    invariant.addToken _ valid lexicalMaximal rfl rfl (by omega)⟩

private theorem recognizeComment
    {file : SourceFile}
    {characters consumed remaining : List Char}
    {offset : Nat}
    {tokens : List Token}
    {comments : List Comment}
    (reached : ReachedCursor file characters offset)
    (invariant : AccumulatorInvariant file offset tokens comments)
    (newComment : Comment)
    (valid : newComment.ValidFor file)
    (startEquation : newComment.span.startByte = offset)
    (endEquation : newComment.span.endByte =
      offset + charactersByteSize consumed)
    (transition : cursorStep file characters offset =
      some (remaining, offset + charactersByteSize consumed)) :
    ReachedCursor file remaining
        (offset + charactersByteSize consumed) ∧
      AccumulatorInvariant file
        (offset + charactersByteSize consumed) tokens
        (newComment :: comments) := by
  exact ⟨reached.advanceFromStep transition,
    invariant.addComment _ valid startEquation endEquation (by omega)⟩

private theorem recognizeLineComment
    {file : SourceFile}
    {rest body remaining : List Char}
    {offset : Nat}
    {tokens : List Token}
    {comments : List Comment}
    (reached : ReachedCursor file ('/' :: '/' :: rest) offset)
    (invariant : AccumulatorInvariant file offset tokens comments)
    (resultEquation :
      takeWhile (· != '\n') rest = (body, remaining)) :
    (let endByte := offset + 2 + charactersByteSize body;
      let newComment : Comment := {
        kind := .line
        span := sourceSpan file offset endByte
      };
      ReachedCursor file remaining endByte ∧
        AccumulatorInvariant file endByte tokens
          (newComment :: comments)) := by
  dsimp only
  have slashSize : '/'.utf8Size = 1 := by decide
  have prefixSize :
      charactersByteSize ('/' :: '/' :: body) =
        2 + charactersByteSize body := by
    simp only [charactersByteSize_cons, slashSize]
    omega
  have recognized := recognizeComment
    (consumed := '/' :: '/' :: body) reached invariant
    ({
      kind := .line
      span := sourceSpan file offset
        (offset + 2 + charactersByteSize body)
    } : Comment)
    (lineCommentValid reached resultEquation)
    rfl
    (by
      simp only [sourceSpan, prefixSize]
      omega)
    (by
      have step :
          cursorStep file ('/' :: '/' :: rest) offset =
            some (remaining,
              offset + 2 + charactersByteSize body) := by
        simp [cursorStep, resultEquation]
      simpa [prefixSize, Nat.add_assoc] using step)
  have computedEnd :
      offset + charactersByteSize ('/' :: '/' :: body) =
        offset + 2 + charactersByteSize body := by
    rw [prefixSize]
    omega
  rw [computedEnd] at recognized
  exact recognized

private theorem recognizeBlockComment
    {file : SourceFile}
    {rest remaining : List Char}
    {offset endByte : Nat}
    {tokens : List Token}
    {comments : List Comment}
    (reached : ReachedCursor file ('/' :: '*' :: rest) offset)
    (invariant : AccumulatorInvariant file offset tokens comments)
    (success :
      skipBlockComment file offset rest 1 (offset + 2) =
        .ok (remaining, endByte)) :
    ReachedCursor file remaining endByte ∧
      AccumulatorInvariant file endByte tokens
        (({
          kind := .block
          span := sourceSpan file offset endByte
        } : Comment) :: comments) := by
  have transition :
      cursorStep file ('/' :: '*' :: rest) offset =
        some (remaining, endByte) := by
    simp [cursorStep, success]
  have valid := blockCommentValid reached success
  obtain ⟨consumed, decomposition, endByteEquation⟩ :=
    skipBlockComment_success_consumed file offset rest remaining
      1 (offset + 2) endByte success
  have progress : offset ≤ endByte := by omega
  exact ⟨reached.advanceFromStep transition,
    invariant.addComment _ valid rfl rfl progress⟩

private theorem recognizeIdentifier
    {file : SourceFile}
    {character : Char}
    {rest tail remaining : List Char}
    {offset : Nat}
    {tokens : List Token}
    {comments : List Comment}
    (reached : ReachedCursor file (character :: rest) offset)
    (invariant : AccumulatorInvariant file offset tokens comments)
    (notWhitespace : isWhitespace character = false)
    (identifierStart : isIdentifierStart character = true)
    (resultEquation :
      takeWhile isIdentifierContinue rest = (tail, remaining)) :
    (let recognizedCharacters := character :: tail;
      let endByte := offset + charactersByteSize recognizedCharacters;
      let kind := classifyIdentifier
        (String.ofList recognizedCharacters);
      ReachedCursor file remaining endByte ∧
        AccumulatorInvariant file endByte
          (token file kind offset endByte :: tokens) comments) := by
  dsimp only
  have partition := takeWhile_partition isIdentifierContinue rest
  rw [resultEquation] at partition
  have decomposition :
      character :: rest =
        (character :: tail) ++ remaining := by
    simp [partition]
  have canonical := classifyIdentifier_implementationCanonical
    character tail identifierStart (by
      have taken := takeWhile_taken_all isIdentifierContinue rest
      rw [resultEquation] at taken
      exact taken)
  have stopped := identifierDoesNotContinue reached decomposition (by
    intro next trailing remainderEquation
    exact takeWhile_remainder_stopped isIdentifierContinue rest
      next trailing (by rw [resultEquation, remainderEquation]))
  have maximal := identifierShapedImplementationMaximal
    (startByte := offset)
    (classifyIdentifier_identifierShaped
      (String.ofList (character :: tail))) stopped
  exact recognizeToken reached invariant decomposition _ canonical
    (classifyIdentifier_text (String.ofList (character :: tail)))
    maximal (by
      have characterNotSlash : character ≠ '/' := by
        intro characterEquation
        subst character
        contradiction
      have characterNotZero : character ≠ '0' := by
        intro characterEquation
        subst character
        contradiction
      simp [cursorStep, characterNotSlash, characterNotZero,
        notWhitespace, identifierStart, resultEquation])

private theorem decimalCursorStep
    {file : SourceFile}
    {character : Char}
    {rest tail remaining : List Char}
    {offset : Nat}
    (notSpecial : ∀ first trailing,
      character :: rest ≠ '0' :: 'x' :: first :: trailing)
    (notWhitespace : isWhitespace character = false)
    (notIdentifierStart : isIdentifierStart character = false)
    (digit : isAsciiDigit character = true)
    (resultEquation :
      takeWhile isAsciiDigit rest = (tail, remaining)) :
    cursorStep file (character :: rest) offset =
      some (remaining,
        offset + charactersByteSize (character :: tail)) := by
  by_cases characterZero : character = '0'
  · subst character
    cases rest with
    | nil =>
        simp [cursorStep, notWhitespace, notIdentifierStart, digit,
          resultEquation]
    | cons next trailing =>
        by_cases nextX : next = 'x'
        · subst next
          cases trailing with
          | nil =>
              simp [cursorStep, notWhitespace, notIdentifierStart, digit,
                resultEquation]
          | cons first remainder =>
              exact False.elim (notSpecial first remainder rfl)
        · simp [cursorStep, nextX, notWhitespace, notIdentifierStart,
            digit, resultEquation]
  · simp [cursorStep, characterZero, notWhitespace,
      notIdentifierStart, digit, resultEquation,
      show character ≠ '/' by
        intro characterSlash
        subst character
        contradiction]

private theorem recognizeDecimal
    {file : SourceFile}
    {character : Char}
    {rest tail remaining : List Char}
    {offset : Nat}
    {tokens : List Token}
    {comments : List Comment}
    (reached : ReachedCursor file (character :: rest) offset)
    (invariant : AccumulatorInvariant file offset tokens comments)
    (notSpecial : ∀ first trailing,
      character :: rest ≠ '0' :: 'x' :: first :: trailing)
    (notWhitespace : isWhitespace character = false)
    (notIdentifierStart : isIdentifierStart character = false)
    (digit : isAsciiDigit character = true)
    (resultEquation :
      takeWhile isAsciiDigit rest = (tail, remaining)) :
    (let digits := character :: tail;
      let text := String.ofList digits;
      let endByte := offset + charactersByteSize digits;
      ReachedCursor file remaining endByte ∧
        AccumulatorInvariant file endByte
          (token file (.decimal text) offset endByte :: tokens) comments) := by
  dsimp only
  have partition := takeWhile_partition isAsciiDigit rest
  rw [resultEquation] at partition
  have decomposition :
      character :: rest =
        (character :: tail) ++ remaining := by
    simp [partition]
  have canonical := decimal_implementationCanonical character tail digit (by
    have taken := takeWhile_taken_all isAsciiDigit rest
    rw [resultEquation] at taken
    exact taken)
  have stopped := decimalDoesNotContinue reached decomposition (by
    intro next trailing remainderEquation
    exact takeWhile_remainder_stopped isAsciiDigit rest
      next trailing (by rw [resultEquation, remainderEquation]))
  have notEligible : String.ofList (character :: tail) = "0" →
      ¬ ImplementationEligibleHexadecimalAt file offset := by
    intro textEquation
    have listEquation := congrArg String.toList textEquation
    simp only [String.toList_ofList] at listEquation
    have characterEquation : character = '0' := by
      simpa using congrArg List.head? listEquation
    subst character
    exact decimalZeroIsNotEligible reached notSpecial
  have maximal := decimalImplementationMaximal stopped notEligible
  exact recognizeToken reached invariant decomposition _ canonical rfl
    maximal (decimalCursorStep notSpecial notWhitespace
      notIdentifierStart digit resultEquation)

private theorem recognizeHexadecimal
    {file : SourceFile}
    {first : Char}
    {rest tail remaining : List Char}
    {offset : Nat}
    {tokens : List Token}
    {comments : List Comment}
    (reached : ReachedCursor file ('0' :: 'x' :: first :: rest) offset)
    (invariant : AccumulatorInvariant file offset tokens comments)
    (firstDigit : isAsciiHexDigit first = true)
    (resultEquation :
      takeWhile isAsciiHexDigit rest = (tail, remaining)) :
    (let digits := first :: tail;
      let text := String.ofList digits;
      let endByte := offset + 2 + charactersByteSize digits;
      ReachedCursor file remaining endByte ∧
        AccumulatorInvariant file endByte
          (token file (.hexadecimal text) offset endByte :: tokens)
          comments) := by
  dsimp only
  have partition := takeWhile_partition isAsciiHexDigit rest
  rw [resultEquation] at partition
  have decomposition :
      '0' :: 'x' :: first :: rest =
        ('0' :: 'x' :: first :: tail) ++ remaining := by
    simp [partition]
  have canonical := hexadecimal_implementationCanonical first tail
    firstDigit (by
      have taken := takeWhile_taken_all isAsciiHexDigit rest
      rw [resultEquation] at taken
      exact taken)
  have stopped := hexadecimalDoesNotContinue reached decomposition (by
    intro next trailing remainderEquation
    exact takeWhile_remainder_stopped isAsciiHexDigit rest
      next trailing (by rw [resultEquation, remainderEquation]))
  have zeroSize : '0'.utf8Size = 1 := by decide
  have xSize : 'x'.utf8Size = 1 := by decide
  have consumedSize :
      charactersByteSize ('0' :: 'x' :: first :: tail) =
        2 + charactersByteSize (first :: tail) := by
    simp only [charactersByteSize_cons, zeroSize, xSize]
    omega
  have endEquation :
      offset + charactersByteSize ('0' :: 'x' :: first :: tail) =
        offset + 2 + charactersByteSize (first :: tail) := by
    rw [consumedSize]
    omega
  have maximal := hexadecimalImplementationMaximal
    (file := file)
    (digits := String.ofList (first :: tail))
    (startByte := offset)
    (endByte := offset +
      charactersByteSize ('0' :: 'x' :: first :: tail)) stopped
  have recognized := recognizeToken reached invariant decomposition _
    canonical (by
      simp only [TokenKind.text, String.ofList_cons]
      rw [show "0x" = "0" ++ "x" by decide,
        show "0" = String.singleton '0' by decide,
        show "x" = String.singleton 'x' by decide,
        String.append_assoc])
    maximal (by
      simp [cursorStep, firstDigit, resultEquation, consumedSize,
        Nat.add_assoc])
  rw [endEquation] at recognized
  exact recognized

private theorem recognizeDecimalZeroBeforeX
    {file : SourceFile}
    {first : Char}
    {rest : List Char}
    {offset : Nat}
    {tokens : List Token}
    {comments : List Comment}
    (reached : ReachedCursor file ('0' :: 'x' :: first :: rest) offset)
    (invariant : AccumulatorInvariant file offset tokens comments)
    (notHexadecimal : isAsciiHexDigit first = false) :
    ReachedCursor file ('x' :: first :: rest) (offset + 1) ∧
      AccumulatorInvariant file (offset + 1)
        (token file (.decimal "0") offset (offset + 1) :: tokens)
        comments := by
  have decomposition :
      '0' :: 'x' :: first :: rest =
        ['0'] ++ ('x' :: first :: rest) := by simp
  have stoppedDecimal := decimalDoesNotContinue reached decomposition (by
    intro next trailing remainderEquation
    cases remainderEquation
    decide)
  have prefixDecomposition :
      '0' :: 'x' :: first :: rest =
        ['0', 'x'] ++ (first :: rest) := by simp
  have stoppedHexadecimal := hexadecimalDoesNotContinue reached
    prefixDecomposition (by
      intro next trailing remainderEquation
      cases remainderEquation
      exact notHexadecimal)
  have zeroSize : charactersByteSize ['0'] = 1 := by decide
  have prefixSize : charactersByteSize ['0', 'x'] = 2 := by decide
  have maximal := decimalImplementationMaximal
    (file := file)
    (digits := "0")
    (startByte := offset)
    (endByte := offset + charactersByteSize ['0'])
    stoppedDecimal
    (by
      intro _ eligible
      have noContinuation :
          ¬ ImplementationHexadecimalContinuesAt file (offset + 2) := by
        simpa [prefixSize] using stoppedHexadecimal
      exact noContinuation eligible.2.2)
  have recognized := recognizeToken reached invariant decomposition
    (.decimal "0") (by decide) (by decide) maximal (by
      simp [cursorStep, notHexadecimal, zeroSize])
  simpa [zeroSize] using recognized

private theorem recognizeWhitespace
    {file : SourceFile}
    {character : Char}
    {rest : List Char}
    {offset : Nat}
    {tokens : List Token}
    {comments : List Comment}
    (reached : ReachedCursor file (character :: rest) offset)
    (invariant : AccumulatorInvariant file offset tokens comments)
    (whitespace : isWhitespace character = true) :
    ReachedCursor file rest (offset + character.utf8Size) ∧
      AccumulatorInvariant file (offset + character.utf8Size)
        tokens comments := by
  have characterNotSlash : character ≠ '/' := by
    intro characterEquation
    subst character
    contradiction
  have characterNotZero : character ≠ '0' := by
    intro characterEquation
    subst character
    contradiction
  have transition :
      cursorStep file (character :: rest) offset =
        some (rest, offset + character.utf8Size) := by
    simp [cursorStep, characterNotSlash, characterNotZero, whitespace]
  exact ⟨reached.advanceFromStep transition,
    invariant.skipWhitespace (by omega)
      (fun index indexAtOrAfter indexBefore =>
        reached.whitespaceByte whitespace indexAtOrAfter indexBefore)⟩

private theorem recognizeAsciiOne
    {file : SourceFile}
    {character : Char}
    {remaining : List Char}
    {offset : Nat}
    {tokens : List Token}
    {comments : List Comment}
    {kind : TokenKind}
    (reached : ReachedCursor file (character :: remaining) offset)
    (invariant : AccumulatorInvariant file offset tokens comments)
    (ascii : character.utf8Size = 1)
    (canonical : implementationIsCanonical kind = true)
    (spelling : kind.text = String.ofList [character])
    (maximal : ImplementationTokenMaximalFor
      (token file kind offset (offset + 1)) file)
    (transition : cursorStep file (character :: remaining) offset =
      some (remaining, offset + 1)) :
    ReachedCursor file remaining (offset + 1) ∧
      AccumulatorInvariant file (offset + 1)
        (token file kind offset (offset + 1) :: tokens) comments := by
  have consumedSize : charactersByteSize [character] = 1 := by
    simp [charactersByteSize, ascii]
  have recognized := recognizeToken
    (consumed := [character]) (remaining := remaining)
    reached invariant (by simp) kind
    canonical spelling
    (by simpa [consumedSize] using maximal)
    (by simpa [consumedSize] using transition)
  simpa [consumedSize] using recognized

private theorem recognizeAsciiTwo
    {file : SourceFile}
    {first second : Char}
    {remaining : List Char}
    {offset : Nat}
    {tokens : List Token}
    {comments : List Comment}
    {kind : TokenKind}
    (reached : ReachedCursor file (first :: second :: remaining) offset)
    (invariant : AccumulatorInvariant file offset tokens comments)
    (firstAscii : first.utf8Size = 1)
    (secondAscii : second.utf8Size = 1)
    (canonical : implementationIsCanonical kind = true)
    (spelling : kind.text = String.ofList [first, second])
    (maximal : ImplementationTokenMaximalFor
      (token file kind offset (offset + 2)) file)
    (transition : cursorStep file (first :: second :: remaining) offset =
      some (remaining, offset + 2)) :
    ReachedCursor file remaining (offset + 2) ∧
      AccumulatorInvariant file (offset + 2)
        (token file kind offset (offset + 2) :: tokens) comments := by
  have consumedSize : charactersByteSize [first, second] = 2 := by
    simp [charactersByteSize, firstAscii, secondAscii]
  have recognized := recognizeToken
    (consumed := [first, second]) (remaining := remaining)
    reached invariant (by simp) kind
    canonical spelling
    (by simpa [consumedSize] using maximal)
    (by simpa [consumedSize] using transition)
  simpa [consumedSize] using recognized

private def lexAux
    (file : SourceFile) :
    Nat → List Char → Nat → List Token → List Comment → Except LexFailure Lexed
  | _, [], _, tokens, comments =>
      .ok {
        tokens := tokens.reverse
        comments := comments.reverse
      }
  | 0, character :: _, offset, _, _ =>
      .error (.internal (.fuelExhausted
        (sourceSpan file offset (offset + character.utf8Size))))
  | fuel + 1, characters, offset, tokens, comments =>
      match characters with
      | [] =>
          .ok {
            tokens := tokens.reverse
            comments := comments.reverse
          }
      | '/' :: '/' :: rest =>
          let (body, remaining) := takeWhile (· != '\n') rest
          let endByte := offset + 2 + charactersByteSize body
          let comment : Comment := {
            kind := .line
            span := sourceSpan file offset endByte
          }
          lexAux file fuel remaining endByte tokens (comment :: comments)
      | '/' :: '*' :: rest =>
          match skipBlockComment file offset rest 1 (offset + 2) with
          | .error error => .error (.source error)
          | .ok (remaining, endByte) =>
              let comment : Comment := {
                kind := .block
                span := sourceSpan file offset endByte
              }
              lexAux file fuel remaining endByte tokens (comment :: comments)
      | '0' :: 'x' :: first :: rest =>
          if isAsciiHexDigit first then
            let (tail, remaining) := takeWhile isAsciiHexDigit rest
            let digits := first :: tail
            let digitText := String.ofList digits
            let endByte := offset + 2 + charactersByteSize digits
            lexAux file fuel remaining endByte
              (token file (.hexadecimal digitText) offset endByte :: tokens) comments
          else
            let endByte := offset + 1
            lexAux file fuel ('x' :: first :: rest) endByte
              (token file (.decimal "0") offset endByte :: tokens) comments
      | character :: rest =>
          if isWhitespace character then
            lexAux file fuel rest (offset + character.utf8Size) tokens comments
          else if isIdentifierStart character then
            let (tail, remaining) := takeWhile isIdentifierContinue rest
            let characters := character :: tail
            let text := String.ofList characters
            let endByte := offset + charactersByteSize characters
            lexAux file fuel remaining endByte
              (token file (classifyIdentifier text) offset endByte :: tokens) comments
          else if isAsciiDigit character then
            let (tail, remaining) := takeWhile isAsciiDigit rest
            let digits := character :: tail
            let digitText := String.ofList digits
            let endByte := offset + charactersByteSize digits
            lexAux file fuel remaining endByte
              (token file (.decimal digitText) offset endByte :: tokens) comments
          else
            match character, rest with
            | '-', '>' :: remaining =>
                lexAux file fuel remaining (offset + 2)
                  (token file .arrow offset (offset + 2) :: tokens) comments
            | '=', '=' :: remaining =>
                lexAux file fuel remaining (offset + 2)
                  (token file .equalEqual offset (offset + 2) :: tokens) comments
            | '!', '=' :: remaining =>
                lexAux file fuel remaining (offset + 2)
                  (token file .bangEqual offset (offset + 2) :: tokens) comments
            | '<', '=' :: remaining =>
                lexAux file fuel remaining (offset + 2)
                  (token file .lessEqual offset (offset + 2) :: tokens) comments
            | '>', '=' :: remaining =>
                lexAux file fuel remaining (offset + 2)
                  (token file .greaterEqual offset (offset + 2) :: tokens) comments
            | '=', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .equal offset (offset + 1) :: tokens) comments
            | '!', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .bang offset (offset + 1) :: tokens) comments
            | '<', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .less offset (offset + 1) :: tokens) comments
            | '>', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .greater offset (offset + 1) :: tokens) comments
            | '+', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .plus offset (offset + 1) :: tokens) comments
            | '-', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .minus offset (offset + 1) :: tokens) comments
            | '*', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .star offset (offset + 1) :: tokens) comments
            | '/', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .slash offset (offset + 1) :: tokens) comments
            | '%', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .percent offset (offset + 1) :: tokens) comments
            | '&', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .ampersand offset (offset + 1) :: tokens) comments
            | '^', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .caret offset (offset + 1) :: tokens) comments
            | '|', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .pipe offset (offset + 1) :: tokens) comments
            | '(', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .leftParen offset (offset + 1) :: tokens) comments
            | ')', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .rightParen offset (offset + 1) :: tokens) comments
            | '{', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .leftBrace offset (offset + 1) :: tokens) comments
            | '}', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .rightBrace offset (offset + 1) :: tokens) comments
            | ':', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .colon offset (offset + 1) :: tokens) comments
            | ';', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .semicolon offset (offset + 1) :: tokens) comments
            | ',', remaining =>
                lexAux file fuel remaining (offset + 1)
                  (token file .comma offset (offset + 1) :: tokens) comments
            | invalid, _ =>
                .error (.source (invalidCharacter file offset invalid))

private theorem lexAux_success_lexes
    (file : SourceFile)
    (fuel : Nat)
    (characters : List Char)
    (offset : Nat)
    (tokens : List Token)
    (comments : List Comment)
    (lexed : Lexed)
    (reached : ReachedCursor file characters offset)
    (invariant : AccumulatorInvariant file offset tokens comments)
    (success :
      lexAux file fuel characters offset tokens comments = .ok lexed) :
    LexicalGrammar.Lexes file lexed := by
  induction fuel generalizing characters offset tokens comments lexed with
  | zero =>
      cases characters with
      | nil =>
          simp only [lexAux, Except.ok.injEq] at success
          subst lexed
          exact invariant.lexesAtEnd reached
      | cons character rest =>
          simp [lexAux] at success
  | succ fuel inductionHypothesis =>
      cases characters with
      | nil =>
          simp only [lexAux, Except.ok.injEq] at success
          subst lexed
          exact invariant.lexesAtEnd reached
      | cons character rest =>
          simp only [lexAux] at success
          split at success
          · simp_all
          · rename_i lineRest linePattern
            simp_all
            let body := (takeWhile (· != '\n') lineRest).1
            let remaining := (takeWhile (· != '\n') lineRest).2
            have resultEquation :
                takeWhile (· != '\n') lineRest = (body, remaining) :=
              (Prod.eta _).symm
            have recognized := recognizeLineComment reached invariant
              resultEquation
            exact inductionHypothesis remaining
              (offset + 2 + charactersByteSize body) tokens _ lexed
              recognized.1 recognized.2 success
          · rename_i blockBody blockPattern
            simp_all
            split at success
            · simp at success
            · rename_i blockRemaining blockEnd blockSuccess
              have recognized := recognizeBlockComment reached invariant
                blockSuccess
              exact inductionHypothesis blockRemaining blockEnd tokens _ lexed
                recognized.1 recognized.2 success
          · rename_i first hexadecimalRest hexadecimalPattern
            simp_all
            split at success
            · rename_i isHexadecimal
              let tail := (takeWhile isAsciiHexDigit hexadecimalRest).1
              let remaining :=
                (takeWhile isAsciiHexDigit hexadecimalRest).2
              have resultEquation :
                  takeWhile isAsciiHexDigit hexadecimalRest =
                    (tail, remaining) := (Prod.eta _).symm
              have recognized := recognizeHexadecimal reached invariant
                isHexadecimal resultEquation
              have recursiveSuccess :
                  lexAux file fuel remaining
                    (offset + 2 + charactersByteSize (first :: tail))
                    (token file
                      (.hexadecimal (String.ofList (first :: tail))) offset
                      (offset + 2 + charactersByteSize (first :: tail)) ::
                        tokens)
                    comments = .ok lexed := by
                simpa [tail, remaining, String.ofList_cons] using success
              exact inductionHypothesis remaining
                (offset + 2 + charactersByteSize (first :: tail)) _ comments
                lexed recognized.1 recognized.2 recursiveSuccess
            · rename_i isNotHexadecimal
              have recognized := recognizeDecimalZeroBeforeX reached
                invariant (Bool.eq_false_iff.mpr isNotHexadecimal)
              exact inductionHypothesis ('x' :: first :: hexadecimalRest)
                (offset + 1) _ comments lexed recognized.1 recognized.2 success
          · rename_i currentRemainder notLineComment notBlockComment generalPattern
            simp_all
            have currentReached :
                ReachedCursor file (character :: rest) offset := by
              simpa [generalPattern.1, generalPattern.2] using reached
            split at success
            · rename_i whitespace
              have currentWhitespace : isWhitespace character = true := by
                simpa [generalPattern.1] using whitespace
              have recognized := recognizeWhitespace currentReached invariant
                currentWhitespace
              have recursiveSuccess :
                  lexAux file fuel rest
                    (offset + character.utf8Size) tokens comments =
                      .ok lexed := by
                simpa [generalPattern.1, generalPattern.2] using success
              exact inductionHypothesis rest
                (offset + character.utf8Size) tokens comments lexed
                recognized.1 recognized.2 recursiveSuccess
            · rename_i notWhitespace
              split at success
              · rename_i identifierStart
                let tail :=
                  (takeWhile isIdentifierContinue rest).1
                let remaining :=
                  (takeWhile isIdentifierContinue rest).2
                have resultEquation :
                    takeWhile isIdentifierContinue rest =
                      (tail, remaining) := (Prod.eta _).symm
                have currentNotWhitespace :
                    isWhitespace character = false := by
                  simpa [generalPattern.1] using
                    (Bool.eq_false_iff.mpr notWhitespace)
                have currentIdentifierStart :
                    isIdentifierStart character = true := by
                  simpa [generalPattern.1] using identifierStart
                have recognized := recognizeIdentifier currentReached invariant
                  currentNotWhitespace currentIdentifierStart
                  resultEquation
                have recursiveSuccess :
                    lexAux file fuel remaining
                      (offset + charactersByteSize (character :: tail))
                      (token file
                        (classifyIdentifier
                          (String.ofList (character :: tail))) offset
                        (offset + charactersByteSize (character :: tail)) ::
                          tokens)
                      comments = .ok lexed := by
                  simpa [generalPattern.1, generalPattern.2, tail, remaining,
                    String.ofList_cons] using success
                exact inductionHypothesis remaining
                  (offset + charactersByteSize (character :: tail)) _
                  comments lexed recognized.1 recognized.2 recursiveSuccess
              · rename_i notIdentifierStart
                split at success
                · rename_i digit
                  let tail := (takeWhile isAsciiDigit rest).1
                  let remaining :=
                    (takeWhile isAsciiDigit rest).2
                  have resultEquation :
                      takeWhile isAsciiDigit rest =
                        (tail, remaining) := (Prod.eta _).symm
                  have currentNotWhitespace :
                      isWhitespace character = false := by
                    simpa [generalPattern.1] using
                      (Bool.eq_false_iff.mpr notWhitespace)
                  have currentNotIdentifierStart :
                      isIdentifierStart character = false := by
                    simpa [generalPattern.1] using
                      (Bool.eq_false_iff.mpr notIdentifierStart)
                  have currentDigit : isAsciiDigit character = true := by
                    simpa [generalPattern.1] using digit
                  have recognized := recognizeDecimal currentReached invariant
                    (by
                      intro specialFirst specialRest specialEquation
                      simp_all)
                    currentNotWhitespace currentNotIdentifierStart currentDigit
                    resultEquation
                  have recursiveSuccess :
                      lexAux file fuel remaining
                        (offset + charactersByteSize (character :: tail))
                        (token file
                          (.decimal (String.ofList (character :: tail))) offset
                          (offset + charactersByteSize (character :: tail)) ::
                            tokens)
                        comments = .ok lexed := by
                    simpa [generalPattern.1, generalPattern.2, tail, remaining,
                      String.ofList_cons] using success
                  exact inductionHypothesis remaining
                    (offset + charactersByteSize (character :: tail)) _
                    comments lexed recognized.1 recognized.2 recursiveSuccess
                · rename_i notDigit
                  split at success <;> simp_all
                  case h_1 =>
                    have recognized := recognizeAsciiTwo
                      (kind := .arrow) reached invariant
                      (by decide) (by decide) (by decide) (by decide)
                      trivial (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_2 =>
                    have recognized := recognizeAsciiTwo
                      (kind := .equalEqual) reached invariant
                      (by decide) (by decide) (by decide) (by decide)
                      trivial (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_3 =>
                    have recognized := recognizeAsciiTwo
                      (kind := .bangEqual) reached invariant
                      (by decide) (by decide) (by decide) (by decide)
                      trivial (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_4 =>
                    have recognized := recognizeAsciiTwo
                      (kind := .lessEqual) reached invariant
                      (by decide) (by decide) (by decide) (by decide)
                      trivial (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_5 =>
                    have recognized := recognizeAsciiTwo
                      (kind := .greaterEqual) reached invariant
                      (by decide) (by decide) (by decide) (by decide)
                      trivial (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_6 noEqual =>
                    have currentReached :
                        ReachedCursor file ('=' :: rest) offset := by
                      simpa [generalPattern.2] using reached
                    have noEqualAfter :
                        ∀ remaining, rest ≠ '=' :: remaining := by
                      intro remaining equality
                      apply noEqual remaining
                      simpa [← generalPattern.2] using equality
                    have maximal : ImplementationTokenMaximalFor
                        (token file .equal offset (offset + 1)) file := by
                      change sourceByteAt file (offset + 1) ≠ some 61
                      have nextNotEqual :=
                        currentReached.byteAfterPrefix_ne_ascii
                          (consumed := ['=']) (remaining := rest) (by simp)
                          '=' 61 (by decide) (by decide) noEqualAfter
                      have equalSize : '='.utf8Size = 1 := by decide
                      simpa [charactersByteSize, equalSize] using nextNotEqual
                    have recognized := recognizeAsciiOne
                      (kind := .equal) currentReached invariant
                      (by decide) (by decide) (by decide) maximal
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    have recursiveSuccess :
                        lexAux file fuel rest (offset + 1)
                          (token file .equal offset (offset + 1) :: tokens)
                          comments = .ok lexed := by
                      simpa [generalPattern.2] using success
                    exact inductionHypothesis rest (offset + 1) _ comments
                      lexed recognized.1 recognized.2 recursiveSuccess
                  case h_7 noEqual =>
                    have currentReached :
                        ReachedCursor file ('!' :: rest) offset := by
                      simpa [generalPattern.2] using reached
                    have noEqualAfter :
                        ∀ remaining, rest ≠ '=' :: remaining := by
                      intro remaining equality
                      apply noEqual remaining
                      simpa [← generalPattern.2] using equality
                    have maximal : ImplementationTokenMaximalFor
                        (token file .bang offset (offset + 1)) file := by
                      change sourceByteAt file (offset + 1) ≠ some 61
                      have nextNotEqual :=
                        currentReached.byteAfterPrefix_ne_ascii
                          (consumed := ['!']) (remaining := rest) (by simp)
                          '=' 61 (by decide) (by decide) noEqualAfter
                      have bangSize : '!'.utf8Size = 1 := by decide
                      simpa [charactersByteSize, bangSize] using nextNotEqual
                    have recognized := recognizeAsciiOne
                      (kind := .bang) currentReached invariant
                      (by decide) (by decide) (by decide) maximal
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    have recursiveSuccess :
                        lexAux file fuel rest (offset + 1)
                          (token file .bang offset (offset + 1) :: tokens)
                          comments = .ok lexed := by
                      simpa [generalPattern.2] using success
                    exact inductionHypothesis rest (offset + 1) _ comments
                      lexed recognized.1 recognized.2 recursiveSuccess
                  case h_8 noEqual =>
                    have currentReached :
                        ReachedCursor file ('<' :: rest) offset := by
                      simpa [generalPattern.2] using reached
                    have noEqualAfter :
                        ∀ remaining, rest ≠ '=' :: remaining := by
                      intro remaining equality
                      apply noEqual remaining
                      simpa [← generalPattern.2] using equality
                    have maximal : ImplementationTokenMaximalFor
                        (token file .less offset (offset + 1)) file := by
                      change sourceByteAt file (offset + 1) ≠ some 61
                      have nextNotEqual :=
                        currentReached.byteAfterPrefix_ne_ascii
                          (consumed := ['<']) (remaining := rest) (by simp)
                          '=' 61 (by decide) (by decide) noEqualAfter
                      have lessSize : '<'.utf8Size = 1 := by decide
                      simpa [charactersByteSize, lessSize] using nextNotEqual
                    have recognized := recognizeAsciiOne
                      (kind := .less) currentReached invariant
                      (by decide) (by decide) (by decide) maximal
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    have recursiveSuccess :
                        lexAux file fuel rest (offset + 1)
                          (token file .less offset (offset + 1) :: tokens)
                          comments = .ok lexed := by
                      simpa [generalPattern.2] using success
                    exact inductionHypothesis rest (offset + 1) _ comments
                      lexed recognized.1 recognized.2 recursiveSuccess
                  case h_9 noEqual =>
                    have currentReached :
                        ReachedCursor file ('>' :: rest) offset := by
                      simpa [generalPattern.2] using reached
                    have noEqualAfter :
                        ∀ remaining, rest ≠ '=' :: remaining := by
                      intro remaining equality
                      apply noEqual remaining
                      simpa [← generalPattern.2] using equality
                    have maximal : ImplementationTokenMaximalFor
                        (token file .greater offset (offset + 1)) file := by
                      change sourceByteAt file (offset + 1) ≠ some 61
                      have nextNotEqual :=
                        currentReached.byteAfterPrefix_ne_ascii
                          (consumed := ['>']) (remaining := rest) (by simp)
                          '=' 61 (by decide) (by decide) noEqualAfter
                      have greaterSize : '>'.utf8Size = 1 := by decide
                      simpa [charactersByteSize, greaterSize] using
                        nextNotEqual
                    have recognized := recognizeAsciiOne
                      (kind := .greater) currentReached invariant
                      (by decide) (by decide) (by decide) maximal
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    have recursiveSuccess :
                        lexAux file fuel rest (offset + 1)
                          (token file .greater offset (offset + 1) :: tokens)
                          comments = .ok lexed := by
                      simpa [generalPattern.2] using success
                    exact inductionHypothesis rest (offset + 1) _ comments
                      lexed recognized.1 recognized.2 recursiveSuccess
                  case h_10 =>
                    have recognized := recognizeAsciiOne
                      (kind := .plus) reached invariant
                      (by decide) (by decide) (by decide) trivial
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_11 noArrow =>
                    have currentReached :
                        ReachedCursor file ('-' :: rest) offset := by
                      simpa [generalPattern.2] using reached
                    have noArrowAfter :
                        ∀ remaining, rest ≠ '>' :: remaining := by
                      intro remaining equality
                      apply noArrow remaining
                      simpa [← generalPattern.2] using equality
                    have maximal : ImplementationTokenMaximalFor
                        (token file .minus offset (offset + 1)) file := by
                      change sourceByteAt file (offset + 1) ≠ some 62
                      have nextNotGreater :=
                        currentReached.byteAfterPrefix_ne_ascii
                          (consumed := ['-']) (remaining := rest) (by simp)
                          '>' 62 (by decide) (by decide) noArrowAfter
                      have minusSize : '-'.utf8Size = 1 := by decide
                      simpa [charactersByteSize, minusSize] using
                        nextNotGreater
                    have recognized := recognizeAsciiOne
                      (kind := .minus) currentReached invariant
                      (by decide) (by decide) (by decide) maximal
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    have recursiveSuccess :
                        lexAux file fuel rest (offset + 1)
                          (token file .minus offset (offset + 1) :: tokens)
                          comments = .ok lexed := by
                      simpa [generalPattern.2] using success
                    exact inductionHypothesis rest (offset + 1) _ comments
                      lexed recognized.1 recognized.2 recursiveSuccess
                  case h_12 =>
                    have recognized := recognizeAsciiOne
                      (kind := .star) reached invariant
                      (by decide) (by decide) (by decide) trivial
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_13 =>
                    have currentReached :
                        ReachedCursor file ('/' :: rest) offset := by
                      simpa [generalPattern.2] using reached
                    have noSlashAfter :
                        ∀ remaining, rest ≠ '/' :: remaining := by
                      intro remaining equality
                      apply currentRemainder remaining
                      simpa [← generalPattern.2] using equality
                    have noStarAfter :
                        ∀ remaining, rest ≠ '*' :: remaining := by
                      intro remaining equality
                      apply notLineComment remaining
                      simpa [← generalPattern.2] using equality
                    have maximal : ImplementationTokenMaximalFor
                        (token file .slash offset (offset + 1)) file := by
                      change sourceByteAt file (offset + 1) ≠ some 47 ∧
                        sourceByteAt file (offset + 1) ≠ some 42
                      have slashSize : '/'.utf8Size = 1 := by decide
                      constructor
                      · have nextNotSlash :=
                          currentReached.byteAfterPrefix_ne_ascii
                            (consumed := ['/']) (remaining := rest) (by simp)
                            '/' 47 (by decide) (by decide) noSlashAfter
                        simpa [charactersByteSize, slashSize] using
                          nextNotSlash
                      · have nextNotStar :=
                          currentReached.byteAfterPrefix_ne_ascii
                            (consumed := ['/']) (remaining := rest) (by simp)
                            '*' 42 (by decide) (by decide) noStarAfter
                        simpa [charactersByteSize, slashSize] using nextNotStar
                    have recognized := recognizeAsciiOne
                      (kind := .slash) currentReached invariant
                      (by decide) (by decide) (by decide) maximal
                      (slashCursorStep file rest offset noSlashAfter noStarAfter)
                    have recursiveSuccess :
                        lexAux file fuel rest (offset + 1)
                          (token file .slash offset (offset + 1) :: tokens)
                          comments = .ok lexed := by
                      simpa [generalPattern.2] using success
                    exact inductionHypothesis rest (offset + 1) _ comments
                      lexed recognized.1 recognized.2 recursiveSuccess
                  case h_14 =>
                    have recognized := recognizeAsciiOne
                      (kind := .percent) reached invariant
                      (by decide) (by decide) (by decide) trivial
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_15 =>
                    have recognized := recognizeAsciiOne
                      (kind := .ampersand) reached invariant
                      (by decide) (by decide) (by decide) trivial
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_16 =>
                    have recognized := recognizeAsciiOne
                      (kind := .caret) reached invariant
                      (by decide) (by decide) (by decide) trivial
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_17 =>
                    have recognized := recognizeAsciiOne
                      (kind := .pipe) reached invariant
                      (by decide) (by decide) (by decide) trivial
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_18 =>
                    have recognized := recognizeAsciiOne
                      (kind := .leftParen) reached invariant
                      (by decide) (by decide) (by decide) trivial
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_19 =>
                    have recognized := recognizeAsciiOne
                      (kind := .rightParen) reached invariant
                      (by decide) (by decide) (by decide) trivial
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_20 =>
                    have recognized := recognizeAsciiOne
                      (kind := .leftBrace) reached invariant
                      (by decide) (by decide) (by decide) trivial
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_21 =>
                    have recognized := recognizeAsciiOne
                      (kind := .rightBrace) reached invariant
                      (by decide) (by decide) (by decide) trivial
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_22 =>
                    have recognized := recognizeAsciiOne
                      (kind := .colon) reached invariant
                      (by decide) (by decide) (by decide) trivial
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_23 =>
                    have recognized := recognizeAsciiOne
                      (kind := .semicolon) reached invariant
                      (by decide) (by decide) (by decide) trivial
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success
                  case h_24 =>
                    have recognized := recognizeAsciiOne
                      (kind := .comma) reached invariant
                      (by decide) (by decide) (by decide) trivial
                      (by simp [cursorStep, notWhitespace,
                        notIdentifierStart, notDigit])
                    exact inductionHypothesis _ _ _ comments lexed
                      recognized.1 recognized.2 success

private inductive ImplementationRejectsAt
    (file : SourceFile) : List Char → Nat → LexError → Prop where
  | invalidCharacter
      (character : Char)
      (remaining : List Char)
      (offset : Nat)
      (notWhitespace : isWhitespace character = false)
      (cannotStart : canStartToken character = false) :
      ImplementationRejectsAt file (character :: remaining) offset
        (invalidCharacter file offset character)
  | unterminatedBlockComment
      (body : List Char)
      (offset : Nat)
      (error : LexError)
      (failure :
        skipBlockComment file offset body 1 (offset + 2) = .error error) :
      ImplementationRejectsAt file ('/' :: '*' :: body) offset error

private theorem invalidCharacter_failure_reached
    {file : SourceFile}
    {character : Char}
    {remaining : List Char}
    {offset : Nat}
    (reached : ReachedCursor file (character :: remaining) offset)
    (notWhitespace : isWhitespace character = false)
    (cannotStart : canStartToken character = false) :
    ∃ cursor,
      ReachedCursor file cursor
          (invalidCharacter file offset character).span.startByte ∧
        ImplementationRejectsAt file cursor
          (invalidCharacter file offset character).span.startByte
          (invalidCharacter file offset character) := by
  refine ⟨character :: remaining, ?_, ?_⟩
  · simpa [invalidCharacter, sourceSpan] using reached
  · simp only [invalidCharacter, sourceSpan]
    exact .invalidCharacter character remaining offset notWhitespace
      cannotStart

private theorem lexAux_source_failure_reached
    (file : SourceFile)
    (fuel : Nat)
    (characters : List Char)
    (offset : Nat)
    (tokens : List Token)
    (comments : List Comment)
    (error : LexError)
    (reached : ReachedCursor file characters offset)
    (failure :
      lexAux file fuel characters offset tokens comments =
        .error (.source error)) :
    ∃ remaining,
      ReachedCursor file remaining error.span.startByte ∧
        ImplementationRejectsAt file remaining error.span.startByte error := by
  induction fuel generalizing characters offset tokens comments error with
  | zero =>
      cases characters <;> simp [lexAux] at failure
  | succ fuel inductionHypothesis =>
      cases characters with
      | nil =>
          simp [lexAux] at failure
      | cons character rest =>
          simp only [lexAux] at failure
          split at failure
          · simp at failure
          · rename_i _ lineRest
            simp_all
            apply inductionHypothesis _ _ _ _ _ ?_ failure
            apply reached.advanceFromStep
            simp [cursorStep]
          · rename_i blockBody _
            simp_all
            split at failure
            · rename_i blockError blockFailure
              simp only [Except.error.injEq, LexFailure.source.injEq]
                at failure
              subst error
              have details :=
                skipBlockComment_failure file offset blockBody 1
                  (offset + 2) blockError blockFailure
              have startEquation : blockError.span.startByte = offset := by
                rw [details.1]
                rfl
              refine ⟨'/' :: '*' :: blockBody, ?_, ?_⟩
              · rw [startEquation]
                exact reached
              · rw [startEquation]
                exact .unterminatedBlockComment blockBody offset
                  blockError blockFailure
            · rename_i blockRemaining blockEnd blockSuccess
              apply inductionHypothesis _ _ _ _ _ ?_ failure
              apply reached.advanceFromStep
              simp [cursorStep, blockSuccess]
          · rename_i _ first hexadecimalRest
            simp_all
            split at failure
            · rename_i isHexadecimal
              apply inductionHypothesis _ _ _ _ _ ?_ failure
              apply reached.advanceFromStep
              simp [cursorStep, isHexadecimal]
            · rename_i isNotHexadecimal
              apply inductionHypothesis _ _ _ _ _ ?_ failure
              apply reached.advanceFromStep
              simp [cursorStep, isNotHexadecimal]
          · rename_i _ currentCharacter currentRest _ _ _
            simp_all
            split at failure
            · rename_i whitespace
              apply inductionHypothesis _ _ _ _ _ ?_ failure
              apply reached.advanceFromStep
              simp [cursorStep, whitespace]
            · rename_i notWhitespace
              split at failure
              · rename_i identifierStart
                apply inductionHypothesis _ _ _ _ _ ?_ failure
                apply reached.advanceFromStep
                simp [cursorStep, notWhitespace, identifierStart]
              · rename_i notIdentifierStart
                split at failure
                · rename_i digit
                  apply inductionHypothesis _ _ _ _ _ ?_ failure
                  apply reached.advanceFromStep
                  simp [cursorStep, notWhitespace, notIdentifierStart,
                    digit]
                · rename_i notDigit
                  split at failure <;> simp_all
                  all_goals try
                    (apply inductionHypothesis _ _ _ _ _ ?_ failure
                     apply reached.advanceFromStep
                     simp [cursorStep, notWhitespace,
                       notIdentifierStart, notDigit])
                  all_goals try
                    (apply slashCursorStep <;> assumption)
                  subst error
                  apply invalidCharacter_failure_reached reached
                    notWhitespace
                  simp_all [canStartToken]

private theorem implementationRejectsAt_rejectsAt
    {file : SourceFile}
    {remaining : List Char}
    {offset : Nat}
    {error : LexError}
    (reached : ReachedCursor file remaining offset)
    (rejection :
      ImplementationRejectsAt file remaining offset error) :
    LexicalGrammar.RejectsAt file offset error := by
  cases rejection with
  | invalidCharacter character trailing offset notWhitespace cannotStart =>
      apply LexicalGrammar.RejectsAt.invalidCharacter character trailing
      · cases reached with
        | intro _ consumedPrefix sourceEquation offsetEquation =>
            rw [sourceEquation, offsetEquation]
            exact LexicalGrammar.charactersAtByteOffset_prefix
              consumedPrefix (character :: trailing)
      · change isWhitespace character = false
        exact notWhitespace
      · change canStartToken character = false
        exact cannotStart
  | unterminatedBlockComment body offset error failure =>
      have details :=
        skipBlockComment_failure file offset body 1 (offset + 2)
          error failure
      have sourceEndEquation :
          file.content.utf8ByteSize =
            offset + 2 + charactersByteSize body := by
        have remainingSize := reached.remainingByteSize
        have slashSize : '/'.utf8Size = 1 := by decide
        have starSize : '*'.utf8Size = 1 := by decide
        simp only [charactersByteSize_cons, slashSize, starSize]
          at remainingSize
        omega
      have errorEquation : error = {
          code := "SL0002"
          span := sourceSpan file offset file.content.utf8ByteSize
          kind := .unterminatedBlockComment
        } := by
        rw [details.1, sourceEndEquation]
      rw [errorEquation]
      apply LexicalGrammar.RejectsAt.unterminatedBlockComment body
      · cases reached with
        | intro _ consumedPrefix sourceEquation offsetEquation =>
            rw [sourceEquation, offsetEquation]
            exact LexicalGrammar.charactersAtByteOffset_prefix
              consumedPrefix ('/' :: '*' :: body)
      · exact
          (blockCommentCloses_agrees
            LexicalGrammar.blockCommentCloses_equation body 1).trans
            details.2

private theorem lexAux_fuel_sufficient
    (file : SourceFile)
    (fuel : Nat)
    (characters : List Char)
    (offset : Nat)
    (tokens : List Token)
    (comments : List Comment)
    (sufficient : characters.length < fuel)
    (span : SourceSpan) :
    lexAux file fuel characters offset tokens comments ≠
      .error (.internal (.fuelExhausted span)) := by
  induction fuel generalizing characters offset tokens comments with
  | zero =>
      omega
  | succ fuel inductionHypothesis =>
      cases characters with
      | nil =>
          simp [lexAux]
      | cons character rest =>
          simp only [lexAux]
          split
          · simp
          · apply inductionHypothesis
            have remainderBound :=
              takeWhile_remainder_length_le (· != '\n') rest.tail
            simp_all
            omega
          · split
            · simp
            · rename_i remaining endByte success
              apply inductionHypothesis
              have remainderBound :=
                skipBlockComment_remainder_length_le
                  file offset _ remaining 1 (offset + 2) endByte success
              simp_all
              omega
          · split
            · apply inductionHypothesis
              have remainderBound :=
                takeWhile_remainder_length_le isAsciiHexDigit (rest.drop 2)
              simp_all
              omega
            · apply inductionHypothesis
              simp_all only [List.cons.injEq, List.length_cons]
              omega
          · split
            · apply inductionHypothesis
              simp_all only [List.cons.injEq, List.length_cons]
              omega
            · split
              · apply inductionHypothesis
                have remainderBound :=
                  takeWhile_remainder_length_le isIdentifierContinue rest
                simp_all
                omega
              · split
                · apply inductionHypothesis
                  have remainderBound :=
                    takeWhile_remainder_length_le isAsciiDigit rest
                  simp_all
                  omega
                · split <;> simp_all <;>
                    apply inductionHypothesis <;> omega

private theorem lexAux_ne_invalid_output
    (file : SourceFile)
    (fuel : Nat)
    (characters : List Char)
    (offset : Nat)
    (tokens : List Token)
    (comments : List Comment)
    (lexed : Lexed) :
    lexAux file fuel characters offset tokens comments ≠
      .error (.internal (.invalidOutput lexed)) := by
  induction fuel generalizing characters offset tokens comments with
  | zero =>
      cases characters <;> simp [lexAux]
  | succ fuel inductionHypothesis =>
      cases characters with
      | nil =>
          simp [lexAux]
      | cons character rest =>
          simp only [lexAux]
          split
          · simp
          · apply inductionHypothesis
          · split
            · simp
            · apply inductionHypothesis
          · split <;> apply inductionHypothesis
          · split
            · apply inductionHypothesis
            · split
              · apply inductionHypothesis
              · split
                · apply inductionHypothesis
                · split <;> simp_all <;> apply inductionHypothesis

private def lexUnchecked (file : SourceFile) : Except LexFailure Lexed :=
  let characters := file.content.toList
  lexAux file (characters.length + 1) characters 0 [] []

private theorem lexUnchecked_success_lexes
    (file : SourceFile)
    (lexed : Lexed)
    (success : lexUnchecked file = .ok lexed) :
    LexicalGrammar.Lexes file lexed := by
  unfold lexUnchecked at success
  exact lexAux_success_lexes file (file.content.toList.length + 1)
    file.content.toList 0 [] [] lexed (ReachedCursor.initial file)
    (AccumulatorInvariant.initial file) success

private theorem lexUnchecked_source_failure_reached
    (file : SourceFile)
    (error : LexError)
    (failure : lexUnchecked file = .error (.source error)) :
    ∃ remaining,
      ReachedCursor file remaining error.span.startByte ∧
        LexicalGrammar.RejectsAt file error.span.startByte error := by
  unfold lexUnchecked at failure
  obtain ⟨remaining, reached, implementationRejection⟩ :=
    lexAux_source_failure_reached file
      (file.content.toList.length + 1) file.content.toList 0 [] []
      error (ReachedCursor.initial file) failure
  exact ⟨remaining, reached,
    implementationRejectsAt_rejectsAt reached implementationRejection⟩

private theorem lexUnchecked_ne_fuel_exhausted
    (file : SourceFile)
    (span : SourceSpan) :
    lexUnchecked file ≠
      .error (.internal (.fuelExhausted span)) := by
  unfold lexUnchecked
  apply lexAux_fuel_sufficient
  omega

private theorem lexUnchecked_ne_invalid_output
    (file : SourceFile)
    (lexed : Lexed) :
    lexUnchecked file ≠
      .error (.internal (.invalidOutput lexed)) := by
  unfold lexUnchecked
  apply lexAux_ne_invalid_output

def lex (file : SourceFile) : Except LexFailure Lexed :=
  match lexUnchecked file with
  | .error failure => .error failure
  | .ok lexed =>
      if LexicalGrammar.accepts file lexed then
        .ok lexed
      else
        .error (.internal (.invalidOutput lexed))

/--
Every source failure produced by the lexer occurs at an implementation-reached
cursor and satisfies the declarative lexical rejection judgment there.
-/
theorem lex_source_failure_sound
    (file : SourceFile)
    (error : LexError)
    (failure : lex file = .error (.source error)) :
    ∃ remaining,
      ReachedCursor file remaining error.span.startByte ∧
        LexicalGrammar.RejectsAt file error.span.startByte error := by
  unfold lex at failure
  cases uncheckedEquation : lexUnchecked file with
  | error uncheckedFailure =>
      simp only [uncheckedEquation] at failure
      cases failure
      exact lexUnchecked_source_failure_reached file error
        uncheckedEquation
  | ok lexed =>
      simp only [uncheckedEquation] at failure
      split at failure <;> simp_all

/-- Every source failure produced by the lexer is recognized by the grammar. -/
theorem lex_source_failure_recognized
    (file : SourceFile)
    (error : LexError)
    (failure : lex file = .error (.source error)) :
    LexicalGrammar.failureAt file error.span.startByte = some error := by
  obtain ⟨_, _, rejection⟩ :=
    lex_source_failure_sound file error failure
  exact (LexicalGrammar.failureAt_eq_some_iff
    file error.span.startByte error).mpr rejection

theorem lex_ne_fuel_exhausted
    (file : SourceFile)
    (span : SourceSpan) :
    lex file ≠ .error (.internal (.fuelExhausted span)) := by
  cases resultEquation : lexUnchecked file with
  | error failure =>
      simp only [lex, resultEquation]
      intro outputEquation
      cases outputEquation
      exact lexUnchecked_ne_fuel_exhausted file span resultEquation
  | ok lexed =>
      simp only [lex, resultEquation]
      split <;> simp

/-- The lexer validation branch cannot reject its own successful output. -/
theorem lex_ne_invalid_output
    (file : SourceFile)
    (lexed : Lexed) :
    lex file ≠ .error (.internal (.invalidOutput lexed)) := by
  cases resultEquation : lexUnchecked file with
  | error failure =>
      simpa [lex, resultEquation] using
        lexUnchecked_ne_invalid_output file lexed
  | ok uncheckedLexed =>
      have lexes := lexUnchecked_success_lexes file uncheckedLexed
        resultEquation
      have accepted :
          LexicalGrammar.accepts file uncheckedLexed = true :=
        (LexicalGrammar.accepts_eq_true_iff file uncheckedLexed).mpr lexes
      simp [lex, resultEquation, accepted]

theorem lex_success_lexes
    (file : SourceFile)
    (lexed : Lexed)
    (success : lex file = .ok lexed) :
    LexicalGrammar.Lexes file lexed := by
  unfold lex at success
  split at success
  · contradiction
  · rename_i unchecked
    split at success
    · rename_i accepted
      cases success
      exact (LexicalGrammar.accepts_eq_true_iff file lexed).mp accepted
    · contradiction

theorem lex_success_valid
    (file : SourceFile)
    (lexed : Lexed)
    (success : lex file = .ok lexed) :
    lexed.ValidFor file :=
  (lex_success_lexes file lexed success).1

end Lexer

end Solcore.Surface
