import Solcore.Surface.Source

set_option autoImplicit false

namespace Solcore.Surface

inductive TokenKind where
  | keywordFunction
  | keywordLet
  | keywordIf
  | keywordElse
  | keywordReturn
  | identifier (text : String)
  | decimal (digits : String)
  | hexadecimal (digits : String)
  | arrow
  | equal
  | equalEqual
  | bang
  | bangEqual
  | less
  | lessEqual
  | greater
  | greaterEqual
  | plus
  | minus
  | star
  | slash
  | percent
  | ampersand
  | caret
  | pipe
  | leftParen
  | rightParen
  | leftBrace
  | rightBrace
  | colon
  | semicolon
  | comma
  deriving Repr, BEq, DecidableEq

namespace TokenKind

private def isAsciiLower (character : Char) : Bool :=
  'a' ≤ character && character ≤ 'z'

private def isAsciiUpper (character : Char) : Bool :=
  'A' ≤ character && character ≤ 'Z'

private def isAsciiDigit (character : Char) : Bool :=
  '0' ≤ character && character ≤ '9'

private def isAsciiLetter (character : Char) : Bool :=
  isAsciiLower character || isAsciiUpper character

private def isAsciiHexDigit (character : Char) : Bool :=
  isAsciiDigit character ||
    ('a' ≤ character && character ≤ 'f') ||
    ('A' ≤ character && character ≤ 'F')

private def isIdentifierText (value : String) : Bool :=
  match value.toList with
  | [] => false
  | first :: rest =>
      isAsciiLetter first &&
        rest.all fun character =>
          isAsciiLetter character || isAsciiDigit character || character = '_'

private def isHardKeyword (value : String) : Bool :=
  value == "function" ||
    value == "let" ||
    value == "if" ||
    value == "else" ||
    value == "return"

def text : TokenKind → String
  | .keywordFunction => "function"
  | .keywordLet => "let"
  | .keywordIf => "if"
  | .keywordElse => "else"
  | .keywordReturn => "return"
  | .identifier value => value
  | .decimal digits => digits
  | .hexadecimal digits => "0x" ++ digits
  | .arrow => "->"
  | .equal => "="
  | .equalEqual => "=="
  | .bang => "!"
  | .bangEqual => "!="
  | .less => "<"
  | .lessEqual => "<="
  | .greater => ">"
  | .greaterEqual => ">="
  | .plus => "+"
  | .minus => "-"
  | .star => "*"
  | .slash => "/"
  | .percent => "%"
  | .ampersand => "&"
  | .caret => "^"
  | .pipe => "|"
  | .leftParen => "("
  | .rightParen => ")"
  | .leftBrace => "{"
  | .rightBrace => "}"
  | .colon => ":"
  | .semicolon => ";"
  | .comma => ","

def isIdentifier : TokenKind → Bool
  | .identifier _ => true
  | _ => false

def isCanonical : TokenKind → Bool
  | .identifier value => isIdentifierText value && !isHardKeyword value
  | .decimal digits =>
      !digits.isEmpty && digits.toList.all isAsciiDigit
  | .hexadecimal digits =>
      !digits.isEmpty && digits.toList.all isAsciiHexDigit
  | _ => true

/-- Raw executable equation for canonical identifier payloads. -/
theorem identifier_isCanonical_equation (value : String) :
    (identifier value).isCanonical =
      ((match value.toList with
      | [] => false
      | first :: rest =>
          ((('a' ≤ first && first ≤ 'z') ||
              ('A' ≤ first && first ≤ 'Z')) &&
            rest.all (fun character =>
              (('a' ≤ character && character ≤ 'z') ||
                ('A' ≤ character && character ≤ 'Z')) ||
              ('0' ≤ character && character ≤ '9') ||
              character = '_'))) &&
        !(value == "function" || value == "let" || value == "if" ||
          value == "else" || value == "return")) := by
  rfl

/-- Raw executable equation for canonical decimal payloads. -/
theorem decimal_isCanonical_equation (digits : String) :
    (decimal digits).isCanonical =
      (!digits.isEmpty && digits.toList.all fun character =>
        '0' ≤ character && character ≤ '9') := by
  rfl

/-- Raw executable equation for canonical hexadecimal payloads. -/
theorem hexadecimal_isCanonical_equation (digits : String) :
    (hexadecimal digits).isCanonical =
      (!digits.isEmpty && digits.toList.all fun character =>
        ('0' ≤ character && character ≤ '9') ||
          ('a' ≤ character && character ≤ 'f') ||
          ('A' ≤ character && character ≤ 'F')) := by
  rfl

def Canonical (kind : TokenKind) : Prop :=
  kind.isCanonical = true

theorem isCanonical_eq_true_iff (kind : TokenKind) :
    kind.isCanonical = true ↔ kind.Canonical := by
  rfl

theorem canonical_text_ne_empty
    (kind : TokenKind)
    (canonical : kind.Canonical) :
    kind.text ≠ "" := by
  cases kind with
  | identifier value =>
      cases characters : value.toList with
      | nil =>
          simp [Canonical, isCanonical, isIdentifierText, characters] at canonical
      | cons first rest =>
          intro empty
          have valueEmpty : value = "" := by simpa [text] using empty
          subst value
          simp at characters
  | decimal digits =>
      simp [Canonical, isCanonical] at canonical
      simpa [text] using canonical.1
  | hexadecimal digits =>
      simp [text]
  | keywordFunction | keywordLet | keywordIf | keywordElse | keywordReturn |
    arrow | equal | equalEqual | bang | bangEqual | less | lessEqual |
    greater | greaterEqual | plus | minus | star | slash | percent |
    ampersand | caret | pipe | leftParen | rightParen | leftBrace |
    rightBrace | colon | semicolon | comma =>
      simp [text]

private theorem identifier_decimal_canonical_disjoint
    (value : String) :
    ¬ ((identifier value).Canonical ∧ (decimal value).Canonical) := by
  intro canonical
  rcases canonical with ⟨identifierCanonical, decimalCanonical⟩
  cases characters : value.toList with
  | nil =>
      simp [Canonical, isCanonical, isIdentifierText, characters] at identifierCanonical
  | cons first rest =>
      simp [Canonical, isCanonical, isIdentifierText, characters,
        isAsciiLetter, isAsciiLower, isAsciiUpper, isAsciiDigit] at identifierCanonical decimalCanonical
      rcases identifierCanonical.1 with lower | upper
      · exact (by decide : ¬ ('a' ≤ '9'))
          (calc
            'a' ≤ first := lower.1
            _ ≤ '9' := decimalCanonical.2.1.2)
      · exact (by decide : ¬ ('A' ≤ '9'))
          (calc
            'A' ≤ first := upper.1
            _ ≤ '9' := decimalCanonical.2.1.2)

theorem eq_of_canonical_of_text_eq
    (first second : TokenKind)
    (firstCanonical : first.Canonical)
    (secondCanonical : second.Canonical)
    (textEquation : first.text = second.text) :
    first = second := by
  cases first <;> cases second <;>
    simp only [text] at textEquation ⊢
  all_goals try { cases textEquation; rfl }
  all_goals try { simp at textEquation }
  all_goals try
    { apply congrArg hexadecimal
      exact (String.append_right_inj "0x").mp textEquation }
  all_goals try
    { have listEquation := congrArg String.toList textEquation
      simp [String.toList_append] at listEquation }
  all_goals cases textEquation
  all_goals try
    { simp_all [Canonical, isCanonical, isIdentifierText, isHardKeyword,
        isAsciiLetter, isAsciiLower, isAsciiUpper, isAsciiDigit,
        isAsciiHexDigit] }
  all_goals try
    { exact False.elim
        ((by decide : ¬ (identifier _).Canonical) firstCanonical) }
  all_goals try
    { exact False.elim
        ((by decide : ¬ (identifier _).Canonical) secondCanonical) }
  all_goals try
    { exact False.elim
        ((by decide : ¬ (decimal _).Canonical) firstCanonical) }
  all_goals try
    { exact False.elim
        ((by decide : ¬ (decimal _).Canonical) secondCanonical) }
  case identifier.decimal.refl =>
    exact False.elim
      (identifier_decimal_canonical_disjoint _
        ⟨firstCanonical, secondCanonical⟩)
  case decimal.identifier.refl =>
    exact False.elim
      (identifier_decimal_canonical_disjoint _
        ⟨secondCanonical, firstCanonical⟩)

private theorem character_toNat_le_of_le
    (character upper : Char)
    (le : character ≤ upper) :
    character.toNat ≤ upper.toNat := by
  change character.val ≤ upper.val at le
  change character.val.toBitVec ≤ upper.val.toBitVec at le
  exact BitVec.le_def.mp le

private theorem asciiLetter_toNat_le
    (character : Char)
    (letter : isAsciiLetter character = true) :
    character.toNat ≤ 127 := by
  simp [isAsciiLetter, isAsciiLower, isAsciiUpper] at letter
  rcases letter with lower | upper
  · exact Nat.le_trans (character_toNat_le_of_le _ _ lower.2) (by decide)
  · exact Nat.le_trans (character_toNat_le_of_le _ _ upper.2) (by decide)

private theorem asciiDigit_toNat_le
    (character : Char)
    (digit : isAsciiDigit character = true) :
    character.toNat ≤ 127 := by
  simp [isAsciiDigit] at digit
  exact Nat.le_trans (character_toNat_le_of_le _ _ digit.2) (by decide)

private theorem asciiHexDigit_toNat_le
    (character : Char)
    (digit : isAsciiHexDigit character = true) :
    character.toNat ≤ 127 := by
  simp [isAsciiHexDigit, isAsciiDigit] at digit
  rcases digit with decimalOrLower | upper
  · rcases decimalOrLower with decimal | lower
    · exact Nat.le_trans (character_toNat_le_of_le _ _ decimal.2) (by decide)
    · exact Nat.le_trans (character_toNat_le_of_le _ _ lower.2) (by decide)
  · exact Nat.le_trans (character_toNat_le_of_le _ _ upper.2) (by decide)

/-- Every character in a canonical token spelling is ASCII. -/
theorem canonical_text_ascii
    (kind : TokenKind)
    (canonical : kind.Canonical) :
    ∀ character ∈ kind.text.toList, character.toNat ≤ 127 := by
  cases kind with
  | identifier value =>
      cases characters : value.toList with
      | nil =>
          simp [Canonical, isCanonical, isIdentifierText, characters] at canonical
      | cons first rest =>
          simp only [Canonical, isCanonical, isIdentifierText, characters,
            Bool.and_eq_true] at canonical
          intro character member
          rw [text, characters] at member
          rcases List.mem_cons.mp member with head | tail
          · rw [head]
            exact asciiLetter_toNat_le first canonical.1.1
          · have allowed := (List.all_eq_true.mp canonical.1.2) character tail
            simp only [Bool.or_eq_true, decide_eq_true_eq] at allowed
            rcases allowed with letterOrDigit | underscore
            · rcases letterOrDigit with letter | digit
              · exact asciiLetter_toNat_le character letter
              · exact asciiDigit_toNat_le character digit
            · rw [underscore]
              decide
  | decimal digits =>
      simp only [Canonical, isCanonical, Bool.and_eq_true] at canonical
      intro character member
      exact asciiDigit_toNat_le character
        ((List.all_eq_true.mp canonical.2) character (by simpa [text] using member))
  | hexadecimal digits =>
      simp only [Canonical, isCanonical, Bool.and_eq_true] at canonical
      intro character member
      simp only [text, String.toList_append] at member
      rcases List.mem_append.mp member with prefixMember | digitsMember
      · simp at prefixMember
        rcases prefixMember with rfl | rfl <;> decide
      · exact asciiHexDigit_toNat_le character
          ((List.all_eq_true.mp canonical.2) character digitsMember)
  | keywordFunction | keywordLet | keywordIf | keywordElse | keywordReturn |
    arrow | equal | equalEqual | bang | bangEqual | less | lessEqual |
    greater | greaterEqual | plus | minus | star | slash | percent |
    ampersand | caret | pipe | leftParen | rightParen | leftBrace |
    rightBrace | colon | semicolon | comma =>
      decide

private theorem utf8EncodeChar_eq_singleton_of_ascii
    (character : Char)
    (ascii : character.toNat ≤ 127) :
    String.utf8EncodeChar character =
      [UInt8.ofNat character.toNat] := by
  simp [String.utf8EncodeChar, ascii]

private theorem ofList_byteArray_eq_map_of_ascii
    (characters : List Char)
    (ascii : ∀ character ∈ characters, character.toNat ≤ 127) :
    (String.ofList characters).toByteArray.data.toList =
      characters.map (fun character => UInt8.ofNat character.toNat) := by
  induction characters with
  | nil =>
      rfl
  | cons character rest inductionHypothesis =>
      simp only [List.mem_cons, forall_eq_or_imp] at ascii
      change (List.utf8Encode (character :: rest)).data.toList = _
      rw [List.utf8Encode_cons, ByteArray.data_append,
        Array.toList_append]
      have singleton :
          (List.utf8Encode [character]).data.toList =
            [UInt8.ofNat character.toNat] := by
        simp [List.utf8Encode,
          utf8EncodeChar_eq_singleton_of_ascii character ascii.1]
      rw [singleton]
      have restEquation := inductionHypothesis ascii.2
      change (List.utf8Encode rest).data.toList = _ at restEquation
      rw [restEquation]
      rfl

private theorem byteArray_eq_map_of_ascii
    (value : String)
    (ascii : ∀ character ∈ value.toList, character.toNat ≤ 127) :
    value.toByteArray.data.toList =
      value.toList.map (fun character => UInt8.ofNat character.toNat) := by
  simpa using ofList_byteArray_eq_map_of_ascii value.toList ascii

/-- The UTF-8 bytes of a canonical token are its ASCII character codes. -/
theorem canonical_text_bytes
    (kind : TokenKind)
    (canonical : kind.Canonical) :
    kind.text.toByteArray.data.toList =
      kind.text.toList.map (fun character => UInt8.ofNat character.toNat) :=
  byteArray_eq_map_of_ascii kind.text (canonical_text_ascii kind canonical)

theorem canonical_text_utf8ByteSize_eq_length
    (kind : TokenKind)
    (canonical : kind.Canonical) :
  kind.text.utf8ByteSize = kind.text.toList.length := by
  have lengths := congrArg List.length (canonical_text_bytes kind canonical)
  rw [Array.length_toList, List.length_map] at lengths
  exact lengths

private theorem char_eq_of_encoded_eq
    (first second : Char)
    (firstAscii : first.toNat ≤ 127)
    (secondAscii : second.toNat ≤ 127)
    (encodedEquation :
      UInt8.ofNat first.toNat = UInt8.ofNat second.toNat) :
    first = second := by
  have natEquation := congrArg UInt8.toNat encodedEquation
  simp [Nat.mod_eq_of_lt (by omega : first.toNat < 256),
    Nat.mod_eq_of_lt (by omega : second.toNat < 256)] at natEquation
  exact Char.toNat_inj.mp natEquation

private theorem charPrefix_of_encodedPrefix
    (first second : List Char)
    (firstAscii : ∀ character ∈ first, character.toNat ≤ 127)
    (secondAscii : ∀ character ∈ second, character.toNat ≤ 127)
    (encodedPrefix :
      first.map (fun character => UInt8.ofNat character.toNat) <+:
        second.map (fun character => UInt8.ofNat character.toNat)) :
    first <+: second := by
  induction first generalizing second with
  | nil =>
      exact ⟨second, rfl⟩
  | cons firstHead firstTail inductionHypothesis =>
      cases second with
      | nil =>
          rcases encodedPrefix with ⟨suffix, equation⟩
          simp at equation
      | cons secondHead secondTail =>
          rcases encodedPrefix with ⟨suffix, equation⟩
          simp only [List.map_cons, List.cons_append] at equation
          have parts := List.cons.inj equation
          have headsEqual := char_eq_of_encoded_eq
            firstHead secondHead
            (firstAscii firstHead (by simp))
            (secondAscii secondHead (by simp)) parts.1
          subst secondHead
          have tailPrefix :
              firstTail.map (fun character => UInt8.ofNat character.toNat) <+:
                secondTail.map (fun character => UInt8.ofNat character.toNat) :=
            ⟨suffix, parts.2⟩
          rcases inductionHypothesis secondTail
              (fun character member => firstAscii character
                (List.mem_cons_of_mem firstHead member))
              (fun character member => secondAscii character
                (List.mem_cons_of_mem firstHead member))
              tailPrefix with ⟨characterSuffix, tailEquation⟩
          exact ⟨characterSuffix, by simp [tailEquation]⟩

/-- Byte-prefix agreement reflects to character-prefix agreement for canonical spellings. -/
theorem text_toList_prefix_of_canonical_of_byte_prefix
    (first second : TokenKind)
    (firstCanonical : first.Canonical)
    (secondCanonical : second.Canonical)
    (bytePrefix :
      first.text.toByteArray.data.toList <+:
        second.text.toByteArray.data.toList) :
    first.text.toList <+: second.text.toList := by
  have firstAscii := canonical_text_ascii first firstCanonical
  have secondAscii := canonical_text_ascii second secondCanonical
  rw [byteArray_eq_map_of_ascii first.text firstAscii,
    byteArray_eq_map_of_ascii second.text secondAscii] at bytePrefix
  exact charPrefix_of_encodedPrefix _ _ firstAscii secondAscii bytePrefix

/-- The character can continue an ASCII identifier spelling. -/
def IdentifierContinueCharacter (character : Char) : Prop :=
  ('a' ≤ character ∧ character ≤ 'z') ∨
    ('A' ≤ character ∧ character ≤ 'Z') ∨
    ('0' ≤ character ∧ character ≤ '9') ∨
    character = '_'

/-- The character can continue a decimal spelling. -/
def DecimalContinueCharacter (character : Char) : Prop :=
  '0' ≤ character ∧ character ≤ '9'

/-- The character can continue a hexadecimal spelling. -/
def HexadecimalContinueCharacter (character : Char) : Prop :=
  DecimalContinueCharacter character ∨
    ('a' ≤ character ∧ character ≤ 'f') ∨
    ('A' ≤ character ∧ character ≤ 'F')

private theorem identifierContinueCharacter_iff
    (character : Char) :
    (isAsciiLetter character || isAsciiDigit character || character = '_') = true ↔
      IdentifierContinueCharacter character := by
  simp [IdentifierContinueCharacter, isAsciiLetter, isAsciiLower,
    isAsciiUpper, isAsciiDigit, or_assoc]

private theorem decimalContinueCharacter_iff
    (character : Char) :
    isAsciiDigit character = true ↔ DecimalContinueCharacter character := by
  simp [DecimalContinueCharacter, isAsciiDigit]

private theorem hexadecimalContinueCharacter_iff
    (character : Char) :
    isAsciiHexDigit character = true ↔
      HexadecimalContinueCharacter character := by
  simp [HexadecimalContinueCharacter, DecimalContinueCharacter,
    isAsciiHexDigit, isAsciiDigit, or_assoc]

private theorem identifierCanonical_characters
    (value : String)
    (canonical : (identifier value).Canonical) :
    ∃ first rest,
      value.toList = first :: rest ∧
      isAsciiLetter first = true ∧
      ∀ character ∈ value.toList,
        IdentifierContinueCharacter character := by
  cases characters : value.toList with
  | nil =>
      simp [Canonical, isCanonical, isIdentifierText, characters] at canonical
  | cons first rest =>
      simp only [Canonical, isCanonical, isIdentifierText, characters,
        Bool.and_eq_true] at canonical
      refine ⟨first, rest, rfl, canonical.1.1, ?_⟩
      intro character member
      rcases List.mem_cons.mp member with head | tail
      · rw [head]
        exact (identifierContinueCharacter_iff first).mp (by
          simp [canonical.1.1])
      · exact (identifierContinueCharacter_iff character).mp
          ((List.all_eq_true.mp canonical.1.2) character tail)

private theorem decimalCanonical_characters
    (value : String)
    (canonical : (decimal value).Canonical) :
    ∃ first rest,
      value.toList = first :: rest ∧
      ∀ character ∈ value.toList,
        DecimalContinueCharacter character := by
  cases characters : value.toList with
  | nil =>
      simp [Canonical, isCanonical, characters] at canonical
      exact False.elim (canonical
        (String.toList_injective (by simpa using characters)))
  | cons first rest =>
      simp only [Canonical, isCanonical, characters, Bool.and_eq_true] at canonical
      refine ⟨first, rest, rfl, ?_⟩
      intro character member
      exact (decimalContinueCharacter_iff character).mp
        ((List.all_eq_true.mp canonical.2) character member)

/-- A canonical hexadecimal payload is nonempty and contains only hexadecimal digits. -/
theorem canonical_hexadecimal_digits
    (value : String)
    (canonical : (hexadecimal value).Canonical) :
    ∃ first rest,
      value.toList = first :: rest ∧
      ∀ character ∈ value.toList,
        HexadecimalContinueCharacter character := by
  cases characters : value.toList with
  | nil =>
      simp [Canonical, isCanonical, characters] at canonical
      exact False.elim (canonical
        (String.toList_injective (by simpa using characters)))
  | cons first rest =>
      simp only [Canonical, isCanonical, characters, Bool.and_eq_true] at canonical
      refine ⟨first, rest, rfl, ?_⟩
      intro character member
      exact (hexadecimalContinueCharacter_iff character).mp
        ((List.all_eq_true.mp canonical.2) character member)

private theorem identifierCanonical_allContinue
    (value : String)
    (canonical : (identifier value).Canonical)
    (character : Char)
    (member : character ∈ value.toList) :
    IdentifierContinueCharacter character := by
  rcases identifierCanonical_characters value canonical with
    ⟨first, rest, characters, firstLetter, allContinue⟩
  exact allContinue character member

private theorem decimalCanonical_allContinue
    (value : String)
    (canonical : (decimal value).Canonical)
    (character : Char)
    (member : character ∈ value.toList) :
    DecimalContinueCharacter character := by
  rcases decimalCanonical_characters value canonical with
    ⟨first, rest, characters, allContinue⟩
  exact allContinue character member

private theorem hexadecimalCanonical_allDigits
    (value : String)
    (canonical : (hexadecimal value).Canonical)
    (character : Char)
    (member : character ∈ value.toList) :
    HexadecimalContinueCharacter character := by
  rcases canonical_hexadecimal_digits value canonical with
    ⟨first, rest, characters, allDigits⟩
  exact allDigits character member

private theorem identifierCanonical_head_of_eq
    (value : String)
    (canonical : (identifier value).Canonical)
    (head : Char)
    (tail : List Char)
    (equation : head :: tail = value.toList) :
    isAsciiLetter head = true := by
  rcases identifierCanonical_characters value canonical with
    ⟨first, rest, characters, firstLetter, allContinue⟩
  rw [characters] at equation
  have heads := (List.cons.inj equation).1
  rw [heads]
  exact firstLetter

private theorem decimalCanonical_head_of_eq
    (value : String)
    (canonical : (decimal value).Canonical)
    (head : Char)
    (tail : List Char)
    (equation : head :: tail = value.toList) :
    isAsciiDigit head = true := by
  rcases decimalCanonical_characters value canonical with
    ⟨first, rest, characters, allContinue⟩
  rw [characters] at equation
  have heads := (List.cons.inj equation).1
  exact (decimalContinueCharacter_iff head).mpr
    (heads ▸ allContinue first (by simp [characters]))

private theorem identifierCanonical_prefix_head
    (value : String)
    (canonical : (identifier value).Canonical)
    (appended : List Char)
    (head : Char)
    (tail : List Char)
    (equation : value.toList ++ appended = head :: tail) :
    isAsciiLetter head = true := by
  rcases identifierCanonical_characters value canonical with
    ⟨first, rest, characters, firstLetter, allContinue⟩
  rw [characters] at equation
  have heads := (List.cons.inj equation).1
  exact heads ▸ firstLetter

private theorem decimalCanonical_prefix_head
    (value : String)
    (canonical : (decimal value).Canonical)
    (appended : List Char)
    (head : Char)
    (tail : List Char)
    (equation : value.toList ++ appended = head :: tail) :
    isAsciiDigit head = true := by
  rcases decimalCanonical_characters value canonical with
    ⟨first, rest, characters, allContinue⟩
  rw [characters] at equation
  have heads := (List.cons.inj equation).1
  exact (decimalContinueCharacter_iff head).mpr
    (heads ▸ allContinue first (by simp [characters]))

private theorem asciiLetter_asciiDigit_disjoint
    (character : Char)
    (letter : isAsciiLetter character = true)
    (digit : isAsciiDigit character = true) :
    False := by
  simp [isAsciiLetter, isAsciiLower, isAsciiUpper, isAsciiDigit] at letter digit
  rcases letter with lower | upper
  · exact (by decide : ¬ ('a' ≤ '9'))
      (calc
        'a' ≤ character := lower.1
        _ ≤ '9' := digit.2)
  · exact (by decide : ¬ ('A' ≤ '9'))
      (calc
        'A' ≤ character := upper.1
        _ ≤ '9' := digit.2)

/-- The only possible way to extend a canonical token spelling. -/
def StrictPrefixContinuationFor
    (first second : TokenKind)
    (next : Char) : Prop :=
  match first with
  | .keywordFunction
  | .keywordLet
  | .keywordIf
  | .keywordElse
  | .keywordReturn
  | .identifier _ => IdentifierContinueCharacter next
  | .decimal digits =>
      DecimalContinueCharacter next ∨
        (digits = "0" ∧
          ∃ hexadecimalDigits,
            second = .hexadecimal hexadecimalDigits ∧ next = 'x')
  | .hexadecimal _ => HexadecimalContinueCharacter next
  | .minus => next = '>'
  | .equal | .bang | .less | .greater => next = '='
  | _ => False

set_option maxHeartbeats 1000000 in
theorem strictPrefixContinuationFor_of_canonical
    (first second : TokenKind)
    (firstCanonical : first.Canonical)
    (secondCanonical : second.Canonical)
    (next : Char)
    (suffix : List Char)
    (textEquation :
      first.text.toList ++ next :: suffix = second.text.toList) :
    StrictPrefixContinuationFor first second next := by
  have textPrefix : first.text.toList <+: second.text.toList :=
    ⟨next :: suffix, textEquation⟩
  have nextMember : next ∈ second.text.toList := by
    rw [← textEquation]
    simp
  cases first <;> cases second <;>
    simp only [text] at textEquation textPrefix nextMember <;>
    simp only [StrictPrefixContinuationFor]
  all_goals try { simp at textEquation }
  all_goals try
    { have stringEquation := congrArg String.ofList textEquation
      simp [String.ofList_append] at stringEquation
      subst_vars }
  all_goals try
    { rcases identifierCanonical_characters _ secondCanonical with
        ⟨secondHead, secondTail, secondCharacters, secondHeadLetter,
          secondAllContinue⟩
      have nextContinues := secondAllContinue next nextMember }
  all_goals try
    { rcases decimalCanonical_characters _ secondCanonical with
        ⟨secondHead, secondTail, secondCharacters, secondAllContinue⟩
      have nextContinues := secondAllContinue next nextMember }
  all_goals try
    { rcases canonical_hexadecimal_digits _ secondCanonical with
        ⟨secondHead, secondTail, secondCharacters, secondAllContinue⟩ }
  all_goals try
    { rcases identifierCanonical_characters _ firstCanonical with
        ⟨firstHead, firstTail, firstCharacters, firstHeadLetter,
          firstAllContinue⟩ }
  all_goals try
    { rcases decimalCanonical_characters _ firstCanonical with
        ⟨firstHead, firstTail, firstCharacters, firstAllContinue⟩ }
  all_goals try
    { rcases canonical_hexadecimal_digits _ firstCanonical with
        ⟨firstHead, firstTail, firstCharacters, firstAllContinue⟩ }
  all_goals try
    { exact identifierCanonical_allContinue _ secondCanonical next nextMember }
  all_goals try
    { exact Or.inl
        (decimalCanonical_allContinue _ secondCanonical next nextMember) }
  all_goals try
    { exact (by decide :
        ∀ character ∈ _, IdentifierContinueCharacter character)
          next nextMember }
  all_goals try
    { have headLetter := identifierCanonical_prefix_head _ firstCanonical
        (next :: suffix) _ _ (by simpa using textEquation)
      exact False.elim
        ((by decide : ¬ isAsciiLetter _ = true) headLetter) }
  all_goals try
    { have headDigit := decimalCanonical_prefix_head _ firstCanonical
        (next :: suffix) _ _ (by simpa using textEquation)
      exact False.elim
        ((by decide : ¬ isAsciiDigit _ = true) headDigit) }
  all_goals try
    { have headLetter := identifierCanonical_head_of_eq _ secondCanonical
        _ _ (by simpa using textEquation)
      exact False.elim
        ((by decide : ¬ isAsciiLetter _ = true) headLetter) }
  all_goals try
    { have headDigit := decimalCanonical_head_of_eq _ secondCanonical
        _ _ (by simpa using textEquation)
      exact False.elim
        ((by decide : ¬ isAsciiDigit _ = true) headDigit) }
  all_goals try
    { simp_all [Canonical, isCanonical, isIdentifierText, isHardKeyword,
        isAsciiLetter, isAsciiLower, isAsciiUpper, isAsciiDigit,
        isAsciiHexDigit, IdentifierContinueCharacter] }
  case identifier.keywordFunction =>
    exact (by simp [IdentifierContinueCharacter] : ∀ character ∈ "function".toList,
      IdentifierContinueCharacter character) next nextMember
  case identifier.keywordLet =>
    exact (by simp [IdentifierContinueCharacter] : ∀ character ∈ "let".toList,
      IdentifierContinueCharacter character) next nextMember
  case identifier.keywordIf =>
    exact (by simp [IdentifierContinueCharacter] : ∀ character ∈ "if".toList,
      IdentifierContinueCharacter character) next nextMember
  case identifier.keywordElse =>
    exact (by simp [IdentifierContinueCharacter] : ∀ character ∈ "else".toList,
      IdentifierContinueCharacter character) next nextMember
  case identifier.keywordReturn =>
    exact (by simp [IdentifierContinueCharacter] : ∀ character ∈ "return".toList,
      IdentifierContinueCharacter character) next nextMember
  case decimal.identifier =>
    rcases decimalCanonical_characters _ firstCanonical with
      ⟨decimalHead, decimalTail, decimalCharacters, decimalAll⟩
    rcases identifierCanonical_characters _ secondCanonical with
      ⟨identifierHead, identifierTail, identifierCharacters,
        identifierHeadLetter, identifierAll⟩
    rw [decimalCharacters, identifierCharacters] at textEquation
    simp only [List.cons_append] at textEquation
    have heads := (List.cons.inj textEquation).1
    have decimalHeadDigit : isAsciiDigit decimalHead = true :=
      (decimalContinueCharacter_iff decimalHead).mpr
        (decimalAll decimalHead (by simp [decimalCharacters]))
    have decimalHeadLetter : isAsciiLetter decimalHead = true := by
      rw [heads]
      exact identifierHeadLetter
    exact False.elim
      (asciiLetter_asciiDigit_disjoint decimalHead
        decimalHeadLetter decimalHeadDigit)
  case decimal.hexadecimal firstDigits secondDigits =>
    rcases decimalCanonical_characters _ firstCanonical with
      ⟨decimalHead, decimalTail, decimalCharacters, decimalAll⟩
    rw [decimalCharacters] at textEquation
    simp only [String.toList_append] at textEquation
    change
      (decimalHead :: decimalTail) ++ next :: suffix =
        '0' :: 'x' :: secondDigits.toList at textEquation
    simp only [List.cons_append] at textEquation
    have headEquation := (List.cons.inj textEquation).1
    have tailEquation := (List.cons.inj textEquation).2
    cases decimalTail with
    | nil =>
        simp only [List.nil_append] at tailEquation
        have nextEquation := (List.cons.inj tailEquation).1
        have digitsEquation : firstDigits = "0" := by
          apply String.toList_injective
          rw [decimalCharacters, headEquation]
          rfl
        exact Or.inr ⟨digitsEquation, secondDigits, rfl, nextEquation⟩
    | cons second rest =>
        simp only [List.cons_append] at tailEquation
        have secondEquation := (List.cons.inj tailEquation).1
        have secondDigit : isAsciiDigit second = true :=
          (decimalContinueCharacter_iff second).mpr
            (decimalAll second (by
              rw [decimalCharacters]
              simp))
        rw [secondEquation] at secondDigit
        contradiction
  case hexadecimal.hexadecimal firstDigits secondDigits =>
    have digitsEquation :
        firstDigits.toList ++ next :: suffix = secondDigits.toList := by
      simpa [String.toList_append] using textEquation
    have nextInDigits : next ∈ secondDigits.toList := by
      rw [← digitsEquation]
      simp
    exact hexadecimalCanonical_allDigits _ secondCanonical next nextInDigits

/-- A canonical token spelling whose first byte is `/` is the slash token. -/
theorem eq_slash_of_canonical_of_firstByte
    (kind : TokenKind)
    (canonical : kind.Canonical)
    (firstByte : kind.text.toByteArray.data.toList[0]? = some 47) :
    kind = .slash := by
  rw [canonical_text_bytes kind canonical] at firstByte
  cases characters : kind.text.toList with
  | nil =>
      simp [characters] at firstByte
  | cons first rest =>
      rw [characters] at firstByte
      simp at firstByte
      have firstAscii := canonical_text_ascii kind canonical first (by
        rw [characters]
        simp)
      have firstIsSlash : first = '/' :=
        char_eq_of_encoded_eq first '/' firstAscii (by decide) (by
          simpa using firstByte)
      subst first
      cases kind with
      | identifier value =>
          have letter := identifierCanonical_head_of_eq value canonical
            '/' rest characters.symm
          contradiction
      | decimal value =>
          have digit := decimalCanonical_head_of_eq value canonical
            '/' rest characters.symm
          contradiction
      | hexadecimal value =>
          simp [text, String.toList_append] at characters
      | slash =>
          rfl
      | keywordFunction | keywordLet | keywordIf | keywordElse | keywordReturn |
        arrow | equal | equalEqual | bang | bangEqual | less | lessEqual |
        greater | greaterEqual | plus | minus | star | percent | ampersand |
        caret | pipe | leftParen | rightParen | leftBrace | rightBrace |
        colon | semicolon | comma =>
          simp [text] at characters

private theorem canonical_text_head_toNat_ge
    (kind : TokenKind)
    (canonical : kind.Canonical)
    (first : Char)
    (rest : List Char)
    (characters : kind.text.toList = first :: rest) :
    33 ≤ first.toNat := by
  cases kind with
  | identifier value =>
      have letter := identifierCanonical_head_of_eq value canonical
        first rest (by simpa [text] using characters.symm)
      simp [isAsciiLetter, isAsciiLower, isAsciiUpper] at letter
      rcases letter with lower | upper
      · exact Nat.le_trans (by decide)
          (character_toNat_le_of_le 'a' first lower.1)
      · exact Nat.le_trans (by decide)
          (character_toNat_le_of_le 'A' first upper.1)
  | decimal value =>
      have digit := decimalCanonical_head_of_eq value canonical
        first rest (by simpa [text] using characters.symm)
      simp [isAsciiDigit] at digit
      exact Nat.le_trans (by decide)
        (character_toNat_le_of_le '0' first digit.1)
  | hexadecimal value =>
      simp [text, String.toList_append] at characters
      rw [← characters.1]
      decide
  | keywordFunction | keywordLet | keywordIf | keywordElse | keywordReturn |
    arrow | equal | equalEqual | bang | bangEqual | less | lessEqual |
    greater | greaterEqual | plus | minus | star | slash | percent |
    ampersand | caret | pipe | leftParen | rightParen | leftBrace |
    rightBrace | colon | semicolon | comma =>
      simp [text] at characters
      rw [← characters.1]
      decide

/-- The first byte of every canonical token spelling is non-whitespace ASCII. -/
theorem canonical_text_firstByte_toNat_ge
    (kind : TokenKind)
    (canonical : kind.Canonical)
    (byte : UInt8)
    (firstByte : kind.text.toByteArray.data.toList[0]? = some byte) :
    33 ≤ byte.toNat := by
  rw [canonical_text_bytes kind canonical] at firstByte
  cases characters : kind.text.toList with
  | nil =>
      simp [characters] at firstByte
  | cons first rest =>
      rw [characters] at firstByte
      simp at firstByte
      have firstAscii := canonical_text_ascii kind canonical first (by
        rw [characters]
        simp)
      have firstLt : first.toNat < 256 := by omega
      rw [← firstByte]
      simpa [UInt8.toNat_ofNat, Nat.mod_eq_of_lt firstLt] using
        canonical_text_head_toNat_ge kind canonical first rest characters

end TokenKind

structure Token where
  kind : TokenKind
  span : SourceSpan
  deriving Repr, BEq, DecidableEq

namespace Token

def text (token : Token) : String :=
  token.kind.text

def ValidFor (token : Token) (file : SourceFile) : Prop :=
  token.kind.Canonical ∧
    token.span.ValidFor file ∧
    file.content.toByteArray.extract token.span.startByte token.span.endByte =
      token.text.toByteArray

def isValidFor (token : Token) (file : SourceFile) : Bool :=
  token.kind.isCanonical &&
    token.span.isValidFor file &&
    decide
      (file.content.toByteArray.extract token.span.startByte token.span.endByte =
        token.text.toByteArray)

theorem isValidFor_eq_true_iff (token : Token) (file : SourceFile) :
    token.isValidFor file = true ↔ token.ValidFor file := by
  simp [isValidFor, ValidFor, TokenKind.isCanonical_eq_true_iff,
    SourceSpan.isValidFor_eq_true_iff, and_assoc]

theorem validFor_startByte_lt_endByte
    (token : Token)
    (file : SourceFile)
    (valid : token.ValidFor file) :
    token.span.startByte < token.span.endByte := by
  have sizeEquation := congrArg ByteArray.size valid.2.2
  rw [ByteArray.size_extract] at sizeEquation
  have endInBounds :
      token.span.endByte ≤ file.content.toByteArray.size := by
    simpa using valid.2.1.2
  rw [Nat.min_eq_left endInBounds, String.size_toByteArray] at sizeEquation
  have textSizePositive : 0 < token.text.utf8ByteSize := by
    rw [Nat.pos_iff_ne_zero]
    intro zero
    exact TokenKind.canonical_text_ne_empty token.kind valid.1
      (String.utf8ByteSize_eq_zero_iff.mp zero)
  omega

/-- Two valid tokens with the same source span are identical. -/
theorem eq_of_validFor_of_span_eq
    (first second : Token)
    (file : SourceFile)
    (firstValid : first.ValidFor file)
    (secondValid : second.ValidFor file)
    (spanEquation : first.span = second.span) :
    first = second := by
  have byteArraysEqual : first.text.toByteArray = second.text.toByteArray := by
    rw [← firstValid.2.2, ← secondValid.2.2, spanEquation]
  have textsEqual : first.kind.text = second.kind.text :=
    String.toByteArray_inj.mp byteArraysEqual
  have kindsEqual := TokenKind.eq_of_canonical_of_text_eq
    first.kind second.kind firstValid.1 secondValid.1 textsEqual
  cases first
  cases second
  simp_all

end Token

inductive CommentKind where
  | line
  | block
  deriving Repr, BEq, DecidableEq

structure Comment where
  kind : CommentKind
  span : SourceSpan
  deriving Repr, BEq, DecidableEq

namespace Comment

private def linePayloadValid : List UInt8 → Bool
  | 47 :: 47 :: body => !(body.contains 10)
  | _ => false

private def blockBodyValid : List UInt8 → Nat → Bool
  | [], _ => false
  | 47 :: 42 :: rest, depth =>
      blockBodyValid rest (depth + 1)
  | 42 :: 47 :: rest, depth =>
      if depth == 1 then
        rest.isEmpty
      else
        blockBodyValid rest (depth - 1)
  | _ :: rest, depth =>
      blockBodyValid rest depth

private theorem blockBodyValid_open
    (rest : List UInt8)
    (depth : Nat) :
    blockBodyValid (47 :: 42 :: rest) depth =
      blockBodyValid rest (depth + 1) := by
  rfl

private theorem blockBodyValid_close
    (rest : List UInt8)
    (depth : Nat) :
    blockBodyValid (42 :: 47 :: rest) depth =
      if depth == 1 then rest.isEmpty
      else blockBodyValid rest (depth - 1) := by
  rfl

private theorem blockBodyValid_other
    (byte : UInt8)
    (rest : List UInt8)
    (depth : Nat)
    (notOpen : ∀ tail, byte = 47 → rest = 42 :: tail → False)
    (notClose : ∀ tail, byte = 42 → rest = 47 :: tail → False) :
    blockBodyValid (byte :: rest) depth = blockBodyValid rest depth := by
  cases rest with
  | nil => simp [blockBodyValid]
  | cons next tail =>
      by_cases byteOpen : byte = 47
      · subst byte
        by_cases nextOpen : next = 42
        · subst next
          exact False.elim (notOpen tail rfl rfl)
        · simp [blockBodyValid]
      · by_cases byteClose : byte = 42
        · subst byte
          by_cases nextClose : next = 47
          · subst next
            exact False.elim (notClose tail rfl rfl)
          · simp [blockBodyValid, nextClose]
        · simp [blockBodyValid]

private def blockPayloadValid : List UInt8 → Bool
  | 47 :: 42 :: rest => blockBodyValid rest 1
  | _ => false

private theorem linePayloadValid_eq_true_iff (payload : List UInt8) :
    linePayloadValid payload = true ↔
      ∃ body, payload = 47 :: 47 :: body ∧ 10 ∉ body := by
  constructor
  · intro valid
    cases payload with
    | nil => simp [linePayloadValid] at valid
    | cons first rest =>
        cases rest with
        | nil => simp [linePayloadValid] at valid
        | cons second body =>
            by_cases firstSlash : first = 47
            · subst first
              by_cases secondSlash : second = 47
              · subst second
                change (!body.contains 10) = true at valid
                exact ⟨body, rfl, by
                  simpa [List.contains_iff_mem] using valid⟩
              · simp [linePayloadValid, secondSlash] at valid
            · simp [linePayloadValid, firstSlash] at valid
  · rintro ⟨body, rfl, noLineFeed⟩
    simp [linePayloadValid, noLineFeed]

private theorem blockPayloadValid_eq_true_iff (payload : List UInt8) :
    blockPayloadValid payload = true ↔
      ∃ body, payload = 47 :: 42 :: body ∧
        blockBodyValid body 1 = true := by
  constructor
  · intro valid
    cases payload with
    | nil => simp [blockPayloadValid] at valid
    | cons first rest =>
        cases rest with
        | nil => simp [blockPayloadValid] at valid
        | cons second body =>
            by_cases firstSlash : first = 47
            · subst first
              by_cases secondStar : second = 42
              · subst second
                exact ⟨body, rfl, valid⟩
              · simp [blockPayloadValid, secondStar] at valid
            · simp [blockPayloadValid, firstSlash] at valid
  · rintro ⟨body, rfl, valid⟩
    exact valid

private theorem linePayloadValid_length
    (payload : List UInt8)
    (valid : linePayloadValid payload = true) :
    2 ≤ payload.length := by
  cases payload with
  | nil => simp [linePayloadValid] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [linePayloadValid] at valid
      | cons second body => simp

private theorem blockPayloadValid_length
    (payload : List UInt8)
    (valid : blockPayloadValid payload = true) :
    2 ≤ payload.length := by
  cases payload with
  | nil => simp [blockPayloadValid] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [blockPayloadValid] at valid
      | cons second body => simp

private theorem blockBodyValid_append_of_valid
    (payload suffix : List UInt8)
    (depth : Nat)
    (valid : blockBodyValid payload depth = true) :
    blockBodyValid (payload ++ suffix) depth = suffix.isEmpty := by
  induction payload, depth using blockBodyValid.induct generalizing suffix with
  | case1 depth => simp [blockBodyValid] at valid
  | case2 rest depth inductionHypothesis =>
      change
        blockBodyValid (47 :: 42 :: (rest ++ suffix)) depth =
          suffix.isEmpty
      rw [blockBodyValid_open]
      change blockBodyValid (rest ++ suffix) (depth + 1) = suffix.isEmpty
      exact inductionHypothesis suffix valid
  | case3 rest depth depthIsOne =>
      rw [blockBodyValid_close] at valid
      change
        (if depth == 1 then (rest ++ suffix).isEmpty
          else blockBodyValid (rest ++ suffix) (depth - 1)) = suffix.isEmpty
      simp only [depthIsOne, if_true] at valid ⊢
      have restEmpty : rest = [] := by
        simpa [List.isEmpty_iff] using valid
      subst rest
      simp
  | case4 rest depth depthIsNotOne inductionHypothesis =>
      rw [blockBodyValid_close] at valid
      change
        (if depth == 1 then (rest ++ suffix).isEmpty
          else blockBodyValid (rest ++ suffix) (depth - 1)) = suffix.isEmpty
      simp only [depthIsNotOne] at valid ⊢
      exact inductionHypothesis suffix valid
  | case5 byte rest depth notOpen notClose inductionHypothesis =>
      rw [blockBodyValid_other byte rest depth notOpen notClose] at valid
      cases rest with
      | nil => simp [blockBodyValid] at valid
      | cons next tail =>
          change
            blockBodyValid (byte :: next :: (tail ++ suffix)) depth =
              suffix.isEmpty
          rw [blockBodyValid_other byte (next :: (tail ++ suffix)) depth]
          · exact inductionHypothesis suffix valid
          · intro appendedTail byteEquation appendedEquation
            apply notOpen tail byteEquation
            exact congrArg (fun head => head :: tail)
              (List.cons.inj appendedEquation).1
          · intro appendedTail byteEquation appendedEquation
            apply notClose tail byteEquation
            exact congrArg (fun head => head :: tail)
              (List.cons.inj appendedEquation).1

private theorem blockPayloadValid_prefix_eq
    (first second : List UInt8)
    (isPrefix : first <+: second)
    (firstValid : blockPayloadValid first = true)
    (secondValid : blockPayloadValid second = true) :
    first = second := by
  rcases isPrefix with ⟨suffix, rfl⟩
  rcases (blockPayloadValid_eq_true_iff first).mp firstValid with
    ⟨body, firstEquation, bodyValid⟩
  subst first
  rcases (blockPayloadValid_eq_true_iff
    ((47 :: 42 :: body) ++ suffix)).mp secondValid with
    ⟨secondBody, secondEquation, secondBodyValid⟩
  have bodyEquation : secondBody = body ++ suffix := by
    simpa using secondEquation.symm
  subst secondBody
  have appended :=
    blockBodyValid_append_of_valid body suffix 1 bodyValid
  rw [appended] at secondBodyValid
  have suffixEmpty : suffix = [] := by
    simpa [List.isEmpty_iff] using secondBodyValid
  subst suffix
  simp

private theorem linePayloadValid_blockPayloadValid_not_prefix
    (linePayload blockPayload : List UInt8)
    (isPrefix : linePayload <+: blockPayload)
    (lineValid : linePayloadValid linePayload = true)
    (blockValid : blockPayloadValid blockPayload = true) :
    False := by
  rcases isPrefix with ⟨suffix, rfl⟩
  rcases (linePayloadValid_eq_true_iff linePayload).mp lineValid with
    ⟨lineBody, lineEquation, noLineFeed⟩
  subst linePayload
  rcases (blockPayloadValid_eq_true_iff
    ((47 :: 47 :: lineBody) ++ suffix)).mp blockValid with
    ⟨blockBody, blockEquation, blockBodyValid⟩
  simp at blockEquation

private theorem blockPayloadValid_linePayloadValid_not_prefix
    (blockPayload linePayload : List UInt8)
    (isPrefix : blockPayload <+: linePayload)
    (blockValid : blockPayloadValid blockPayload = true)
    (lineValid : linePayloadValid linePayload = true) :
    False := by
  rcases isPrefix with ⟨suffix, rfl⟩
  rcases (blockPayloadValid_eq_true_iff blockPayload).mp blockValid with
    ⟨blockBody, blockEquation, blockBodyValid⟩
  subst blockPayload
  rcases (linePayloadValid_eq_true_iff
    ((47 :: 42 :: blockBody) ++ suffix)).mp lineValid with
    ⟨lineBody, lineEquation, noLineFeed⟩
  simp at lineEquation

def payloadValid (comment : Comment) (file : SourceFile) : Bool :=
  let sourceBytes := file.content.toByteArray
  let payload :=
    (sourceBytes.extract comment.span.startByte comment.span.endByte).data.toList
  match comment.kind with
  | .line =>
      linePayloadValid payload &&
        (comment.span.endByte == sourceBytes.size ||
          sourceBytes.data[comment.span.endByte]? == some 10)
  | .block =>
      blockPayloadValid payload

/-- Raw executable equation for a retained line-comment payload. -/
theorem line_payload_valid_equation
    (file : SourceFile)
    (span : SourceSpan) :
    payloadValid { kind := .line, span := span } file =
      let sourceBytes := file.content.toByteArray
      let payload :=
        (sourceBytes.extract span.startByte span.endByte).data.toList
      (match payload with
      | 47 :: 47 :: body => !(body.contains 10)
      | _ => false) &&
        (span.endByte == sourceBytes.size ||
          sourceBytes.data[span.endByte]? == some 10) := by
  rfl

/-- Raw executable equation for a retained block-comment payload. -/
theorem block_payload_valid_equation
    (file : SourceFile)
    (span : SourceSpan) :
    payloadValid { kind := .block, span := span } file =
      let sourceBytes := file.content.toByteArray
      let payload :=
        (sourceBytes.extract span.startByte span.endByte).data.toList
      match payload with
      | 47 :: 42 :: rest => blockBodyValid rest 1
      | _ => false := by
  rfl

/-- One-step executable equation for nested block-comment bodies. -/
theorem blockBodyValid_equation
    (bytes : List UInt8)
    (depth : Nat) :
    blockBodyValid bytes depth =
      match bytes with
      | [] => false
      | 47 :: 42 :: rest => blockBodyValid rest (depth + 1)
      | 42 :: 47 :: rest =>
          if depth == 1 then rest.isEmpty
          else blockBodyValid rest (depth - 1)
      | _ :: rest => blockBodyValid rest depth := by
  rw [blockBodyValid.eq_def]
  cases bytes with
  | nil =>
      rfl
  | cons first rest =>
      cases rest with
      | nil =>
          by_cases firstSlash : first = 47
          · subst first
            rfl
          · by_cases firstStar : first = 42
            · subst first
              rfl
            · simp
      | cons second trailing =>
          by_cases firstSlash : first = 47
          · subst first
            by_cases secondStar : second = 42
            · subst second
              rfl
            · simp [secondStar]
          · by_cases firstStar : first = 42
            · subst first
              by_cases secondSlash : second = 47
              · subst second
                rfl
              · simp [firstSlash, secondSlash]
            · simp [firstSlash, firstStar]

def ValidFor (comment : Comment) (file : SourceFile) : Prop :=
  comment.span.ValidFor file ∧ comment.payloadValid file = true

def isValidFor (comment : Comment) (file : SourceFile) : Bool :=
  comment.span.isValidFor file && comment.payloadValid file

theorem isValidFor_eq_true_iff (comment : Comment) (file : SourceFile) :
    comment.isValidFor file = true ↔ comment.ValidFor file := by
  simp [isValidFor, ValidFor, SourceSpan.isValidFor_eq_true_iff]

theorem validFor_startByte_lt_endByte
    (comment : Comment)
    (file : SourceFile)
    (valid : comment.ValidFor file) :
    comment.span.startByte < comment.span.endByte := by
  have endInBounds :
      comment.span.endByte ≤ file.content.toByteArray.size := by
    simpa using valid.1.2
  have extractedSize :
      (file.content.toByteArray.extract
        comment.span.startByte comment.span.endByte).size =
        comment.span.endByte - comment.span.startByte := by
    rw [ByteArray.size_extract, Nat.min_eq_left endInBounds]
  have payloadLength :
      2 ≤
        (file.content.toByteArray.extract
          comment.span.startByte comment.span.endByte).data.toList.length := by
    cases kindEquation : comment.kind with
    | line =>
        have payloadValidity := valid.2
        simp only [payloadValid, kindEquation] at payloadValidity
        rw [Bool.and_eq_true] at payloadValidity
        exact linePayloadValid_length _ payloadValidity.1
    | block =>
        have payloadValidity := valid.2
        simp only [payloadValid, kindEquation] at payloadValidity
        exact blockPayloadValid_length _ payloadValidity
  have payloadArrayLength :
      (file.content.toByteArray.extract
        comment.span.startByte comment.span.endByte).data.toList.length =
        (file.content.toByteArray.extract
          comment.span.startByte comment.span.endByte).size := by
    exact Array.length_toList
  rw [payloadArrayLength, extractedSize] at payloadLength
  omega

/-- Every valid retained comment payload begins with its two-byte opener. -/
theorem validFor_payload_opener
    (comment : Comment)
    (file : SourceFile)
    (valid : comment.ValidFor file) :
    ∃ second body,
      (file.content.toByteArray.extract
        comment.span.startByte comment.span.endByte).data.toList =
          47 :: second :: body ∧
      ((comment.kind = .line ∧ second = 47) ∨
        (comment.kind = .block ∧ second = 42)) := by
  cases kindEquation : comment.kind with
  | line =>
      have payloadValidity := valid.2
      simp only [payloadValid, kindEquation] at payloadValidity
      rw [Bool.and_eq_true] at payloadValidity
      rcases (linePayloadValid_eq_true_iff _).mp payloadValidity.1 with
        ⟨body, payloadEquation, noLineFeed⟩
      exact ⟨47, body, payloadEquation, Or.inl ⟨rfl, rfl⟩⟩
  | block =>
      have payloadValidity := valid.2
      simp only [payloadValid, kindEquation] at payloadValidity
      rcases (blockPayloadValid_eq_true_iff _).mp payloadValidity with
        ⟨body, payloadEquation, bodyValid⟩
      exact ⟨42, body, payloadEquation, Or.inr ⟨rfl, rfl⟩⟩

private def sourcePayload (comment : Comment) (file : SourceFile) : List UInt8 :=
  (file.content.toByteArray.extract
    comment.span.startByte comment.span.endByte).data.toList

private theorem sourceSpan_eq_of_fields_eq
    (first second : SourceSpan)
    (sourceEquation : first.source = second.source)
    (startEquation : first.startByte = second.startByte)
    (endEquation : first.endByte = second.endByte) :
    first = second := by
  cases first
  cases second
  simp_all

private theorem comment_eq_of_fields_eq
    (first second : Comment)
    (kindEquation : first.kind = second.kind)
    (spanEquation : first.span = second.span) :
    first = second := by
  cases first
  cases second
  simp_all

private theorem extractPayload_prefix_of_start_eq_of_end_le
    (first second : Comment)
    (file : SourceFile)
    (startEquation : first.span.startByte = second.span.startByte)
    (endLe : first.span.endByte ≤ second.span.endByte) :
    sourcePayload first file <+: sourcePayload second file := by
  unfold sourcePayload
  rw [startEquation]
  simpa [ByteArray.data_extract, Array.toList_extract] using
    (List.take_prefix_take_left
      (l := List.drop second.span.startByte
        file.content.toByteArray.data.toList)
      (Nat.sub_le_sub_right endLe second.span.startByte))

private theorem extractPayload_getElem?_eq_source
    (comment : Comment)
    (file : SourceFile)
    (index : Nat)
    (startLe : comment.span.startByte ≤ index)
    (indexLt : index < comment.span.endByte) :
    (sourcePayload comment file)[index - comment.span.startByte]? =
      file.content.toByteArray.data[index]? := by
  unfold sourcePayload
  rw [← Array.getElem?_toList]
  simp only [ByteArray.data_extract, Array.toList_extract]
  rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop]
  congr 1
  omega

private theorem endByte_eq_of_payload_eq
    (first second : Comment)
    (file : SourceFile)
    (firstValid : first.ValidFor file)
    (secondValid : second.ValidFor file)
    (startEquation : first.span.startByte = second.span.startByte)
    (payloadEquation : sourcePayload first file = sourcePayload second file) :
    first.span.endByte = second.span.endByte := by
  have lengthEquation := congrArg List.length payloadEquation
  unfold sourcePayload at lengthEquation
  simp only [Array.length_toList] at lengthEquation
  change
    (file.content.toByteArray.extract
      first.span.startByte first.span.endByte).size =
    (file.content.toByteArray.extract
      second.span.startByte second.span.endByte).size at lengthEquation
  rw [ByteArray.size_extract, ByteArray.size_extract] at lengthEquation
  have firstEndInBounds :
      first.span.endByte ≤ file.content.toByteArray.size := by
    simpa using firstValid.1.2
  have secondEndInBounds :
      second.span.endByte ≤ file.content.toByteArray.size := by
    simpa using secondValid.1.2
  rw [Nat.min_eq_left firstEndInBounds,
    Nat.min_eq_left secondEndInBounds] at lengthEquation
  rw [startEquation] at lengthEquation
  have firstOrdered := firstValid.1.1.2
  have secondOrdered := secondValid.1.1.2
  omega

private theorem eq_of_validFor_of_startByte_eq_of_endByte_le
    (first second : Comment)
    (file : SourceFile)
    (firstValid : first.ValidFor file)
    (secondValid : second.ValidFor file)
    (startEquation : first.span.startByte = second.span.startByte)
    (endLe : first.span.endByte ≤ second.span.endByte) :
    first = second := by
  have payloadPrefix :=
    extractPayload_prefix_of_start_eq_of_end_le
      first second file startEquation endLe
  have firstPayloadValidity := firstValid.2
  have secondPayloadValidity := secondValid.2
  cases firstKind : first.kind <;> cases secondKind : second.kind
  · simp only [payloadValid, firstKind] at firstPayloadValidity
    simp only [payloadValid, secondKind] at secondPayloadValidity
    rw [Bool.and_eq_true] at firstPayloadValidity secondPayloadValidity
    have firstLineValid := firstPayloadValidity.1
    have secondLineValid := secondPayloadValidity.1
    have endsEqual : first.span.endByte = second.span.endByte := by
      by_cases strict : first.span.endByte < second.span.endByte
      · have secondEndInBounds :
            second.span.endByte ≤ file.content.toByteArray.size := by
          simpa using secondValid.1.2
        have firstNotEof :
            first.span.endByte ≠ file.content.toByteArray.size := by
          omega
        have firstTerminator :
            file.content.toByteArray.data[first.span.endByte]? = some 10 := by
          have endCondition := firstPayloadValidity.2
          simp at endCondition
          rcases endCondition with atEof | lineFeed
          · exact False.elim (firstNotEof (by simpa using atEof))
          · exact lineFeed
        rcases (linePayloadValid_eq_true_iff _).mp secondLineValid with
          ⟨body, bodyEquation, noLineFeed⟩
        have lookup := extractPayload_getElem?_eq_source
          second file first.span.endByte (by
            rw [← startEquation]
            exact firstValid.1.1.2) strict
        rw [firstTerminator] at lookup
        have lineFeedInPayload : (10 : UInt8) ∈ sourcePayload second file :=
          (List.mem_iff_getElem?).mpr
            ⟨first.span.endByte - second.span.startByte, lookup⟩
        change sourcePayload second file = 47 :: 47 :: body at bodyEquation
        rw [bodyEquation] at lineFeedInPayload
        simp at lineFeedInPayload
        exact (noLineFeed lineFeedInPayload).elim
      · omega
    have payloadEquation :
        sourcePayload first file = sourcePayload second file := by
      unfold sourcePayload
      rw [startEquation, endsEqual]
    have spanEquation : first.span = second.span := by
      exact sourceSpan_eq_of_fields_eq first.span second.span
        (firstValid.1.1.1.trans secondValid.1.1.1.symm)
        startEquation endsEqual
    exact comment_eq_of_fields_eq first second
      (firstKind.trans secondKind.symm) spanEquation
  · simp only [payloadValid, firstKind] at firstPayloadValidity
    simp only [payloadValid, secondKind] at secondPayloadValidity
    rw [Bool.and_eq_true] at firstPayloadValidity
    exact False.elim
      (linePayloadValid_blockPayloadValid_not_prefix
        _ _ payloadPrefix firstPayloadValidity.1 secondPayloadValidity)
  · simp only [payloadValid, firstKind] at firstPayloadValidity
    simp only [payloadValid, secondKind] at secondPayloadValidity
    rw [Bool.and_eq_true] at secondPayloadValidity
    exact False.elim
      (blockPayloadValid_linePayloadValid_not_prefix
        _ _ payloadPrefix firstPayloadValidity secondPayloadValidity.1)
  · simp only [payloadValid, firstKind] at firstPayloadValidity
    simp only [payloadValid, secondKind] at secondPayloadValidity
    have payloadEquation :=
      blockPayloadValid_prefix_eq _ _ payloadPrefix
        firstPayloadValidity secondPayloadValidity
    have endEquation := endByte_eq_of_payload_eq
      first second file firstValid secondValid startEquation payloadEquation
    have spanEquation : first.span = second.span := by
      exact sourceSpan_eq_of_fields_eq first.span second.span
        (firstValid.1.1.1.trans secondValid.1.1.1.symm)
        startEquation endEquation
    exact comment_eq_of_fields_eq first second
      (firstKind.trans secondKind.symm) spanEquation

/-- Two valid retained comments beginning at the same byte are identical. -/
theorem eq_of_validFor_of_startByte_eq
    (first second : Comment)
    (file : SourceFile)
    (firstValid : first.ValidFor file)
    (secondValid : second.ValidFor file)
    (startEquation : first.span.startByte = second.span.startByte) :
    first = second := by
  rcases Nat.le_total first.span.endByte second.span.endByte with
    endLe | endLe
  · exact eq_of_validFor_of_startByte_eq_of_endByte_le
      first second file firstValid secondValid startEquation endLe
  · exact (eq_of_validFor_of_startByte_eq_of_endByte_le
      second first file secondValid firstValid startEquation.symm endLe).symm

end Comment

structure Lexed where
  tokens : List Token
  comments : List Comment
  deriving Repr, BEq, DecidableEq

namespace Lexed

private def spansOrdered : List SourceSpan → Bool
  | [] | [_] => true
  | first :: second :: rest =>
      first.endByte ≤ second.startByte &&
        spansOrdered (second :: rest)

private def spansDisjoint (first second : SourceSpan) : Bool :=
  first.endByte ≤ second.startByte ||
    second.endByte ≤ first.startByte

private def crossDisjoint (lexed : Lexed) : Bool :=
  lexed.tokens.all fun token =>
    lexed.comments.all fun comment =>
      spansDisjoint token.span comment.span

private def isAsciiWhitespaceByte (byte : UInt8) : Bool :=
  byte == 9 || byte == 10 || byte == 12 || byte == 13 || byte == 32

private def coversByte (span : SourceSpan) (index : Nat) : Bool :=
  span.startByte ≤ index && index < span.endByte

private def sourcePartitioned (lexed : Lexed) (file : SourceFile) : Bool :=
  let spans :=
    lexed.tokens.map (·.span) ++ lexed.comments.map (·.span)
  let bytes := file.content.toByteArray
  (List.range bytes.size).all fun index =>
    spans.any (fun span => coversByte span index) ||
      match bytes.data[index]? with
      | some byte => isAsciiWhitespaceByte byte
      | none => false

/-- Adjacent spans occur in source order and do not overlap. -/
def SpansOrdered : List SourceSpan → Prop
  | [] | [_] => True
  | first :: second :: rest =>
      first.endByte ≤ second.startByte ∧
        SpansOrdered (second :: rest)

/-- Two half-open spans do not overlap. -/
def SpansDisjoint (first second : SourceSpan) : Prop :=
  first.endByte ≤ second.startByte ∨
    second.endByte ≤ first.startByte

/-- Every token span is disjoint from every retained comment span. -/
def CrossDisjoint (lexed : Lexed) : Prop :=
  ∀ token ∈ lexed.tokens, ∀ comment ∈ lexed.comments,
    SpansDisjoint token.span comment.span

/-- The byte belongs to the ASCII whitespace class skipped by the lexer. -/
def IsAsciiWhitespaceByte (byte : UInt8) : Prop :=
  byte = 9 ∨ byte = 10 ∨ byte = 12 ∨ byte = 13 ∨ byte = 32

/-- The index belongs to a half-open source span. -/
def CoversByte (span : SourceSpan) (index : Nat) : Prop :=
  span.startByte ≤ index ∧ index < span.endByte

/--
Every source byte is owned by a token or comment, or is ASCII whitespace.
-/
def SourcePartitioned (lexed : Lexed) (file : SourceFile) : Prop :=
  ∀ index, index < file.content.toByteArray.size →
    (∃ token ∈ lexed.tokens, CoversByte token.span index) ∨
    (∃ comment ∈ lexed.comments, CoversByte comment.span index) ∨
    ∃ byte,
      file.content.toByteArray.data[index]? = some byte ∧
        IsAsciiWhitespaceByte byte

theorem spansOrdered_eq_true_iff (spans : List SourceSpan) :
    spansOrdered spans = true ↔ SpansOrdered spans := by
  induction spans with
  | nil => simp [spansOrdered, SpansOrdered]
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil => simp [spansOrdered, SpansOrdered]
      | cons second tail =>
          simp [spansOrdered, SpansOrdered, inductionHypothesis]

theorem spansDisjoint_eq_true_iff (first second : SourceSpan) :
    spansDisjoint first second = true ↔ SpansDisjoint first second := by
  simp [spansDisjoint, SpansDisjoint]

theorem crossDisjoint_eq_true_iff (lexed : Lexed) :
    crossDisjoint lexed = true ↔ CrossDisjoint lexed := by
  simp [crossDisjoint, CrossDisjoint, spansDisjoint_eq_true_iff]

theorem isAsciiWhitespaceByte_eq_true_iff (byte : UInt8) :
    isAsciiWhitespaceByte byte = true ↔ IsAsciiWhitespaceByte byte := by
  simp [isAsciiWhitespaceByte, IsAsciiWhitespaceByte, or_assoc]

theorem coversByte_eq_true_iff (span : SourceSpan) (index : Nat) :
    coversByte span index = true ↔ CoversByte span index := by
  simp [coversByte, CoversByte]

theorem sourcePartitioned_eq_true_iff (lexed : Lexed) (file : SourceFile) :
    sourcePartitioned lexed file = true ↔ SourcePartitioned lexed file := by
  constructor
  · intro checked index inBounds
    simp [sourcePartitioned, coversByte_eq_true_iff] at checked
    specialize checked index inBounds
    rcases checked with (covered | whitespace)
    · rcases covered with (token | comment)
      · exact Or.inl token
      · exact Or.inr (Or.inl comment)
    · generalize byteAt : file.content.toByteArray.data[index]? = byte
          at whitespace
      cases byte with
      | none => contradiction
      | some byte =>
          exact Or.inr (Or.inr ⟨byte, rfl,
            (isAsciiWhitespaceByte_eq_true_iff byte).mp whitespace⟩)
  · intro partitioned
    simp [sourcePartitioned, coversByte_eq_true_iff]
    intro index inBounds
    rcases partitioned index inBounds with
      (token | comment | ⟨byte, byteAt, whitespace⟩)
    · exact Or.inl (Or.inl token)
    · exact Or.inl (Or.inr comment)
    · exact Or.inr (by
        rw [byteAt]
        exact (isAsciiWhitespaceByte_eq_true_iff byte).mpr whitespace)

def ValidFor (lexed : Lexed) (file : SourceFile) : Prop :=
  (∀ token ∈ lexed.tokens, token.ValidFor file) ∧
    (∀ comment ∈ lexed.comments, comment.ValidFor file) ∧
    SpansOrdered (lexed.tokens.map (·.span)) ∧
    SpansOrdered (lexed.comments.map (·.span)) ∧
    CrossDisjoint lexed ∧
    SourcePartitioned lexed file

def isValidFor (lexed : Lexed) (file : SourceFile) : Bool :=
  lexed.tokens.all (·.isValidFor file) &&
    lexed.comments.all (·.isValidFor file) &&
    spansOrdered (lexed.tokens.map (·.span)) &&
    spansOrdered (lexed.comments.map (·.span)) &&
    crossDisjoint lexed &&
    sourcePartitioned lexed file

def spansValidFor (lexed : Lexed) (file : SourceFile) : Bool :=
  lexed.isValidFor file

theorem isValidFor_eq_true_iff (lexed : Lexed) (file : SourceFile) :
    lexed.isValidFor file = true ↔ lexed.ValidFor file := by
  simp [isValidFor, ValidFor, Token.isValidFor_eq_true_iff,
    Comment.isValidFor_eq_true_iff, spansOrdered_eq_true_iff,
    crossDisjoint_eq_true_iff, sourcePartitioned_eq_true_iff, and_assoc]

theorem spansValidFor_eq_true_iff (lexed : Lexed) (file : SourceFile) :
    lexed.spansValidFor file = true ↔ lexed.ValidFor file := by
  exact isValidFor_eq_true_iff lexed file

end Lexed

end Solcore.Surface
