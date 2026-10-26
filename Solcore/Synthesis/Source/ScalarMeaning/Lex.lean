/-! Tokens of the source fragment and a lexer over characters. Spaces
and newlines only separate tokens. Identifiers are ASCII letters, digits and
underscores not starting with a digit; numbers are unsigned decimal; `==` is a
single token and every other operator or delimiter is one character. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

inductive Token where
  | ident (text : String)
  | number (value : Nat)
  | symbol (char : Char)
  | equalEqual
  deriving Repr, BEq, DecidableEq

def blankChars : List Char := [' ', '\n']

def decimalDigits : List Char := ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

def identifierStarts : List Char :=
  ['_', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q',
    'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I',
    'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z']

/-- Single-character tokens other than `=`. -/
def symbolChars : List Char :=
  ['(', ')', '{', '}', ';', ':', ',', '.', '+', '-', '*', '&', '|', '^', '~', '!', '>', '<']

def isBlank (char : Char) : Bool := blankChars.contains char
def isDigitChar (char : Char) : Bool := decimalDigits.contains char
def isIdentStart (char : Char) : Bool := identifierStarts.contains char
def isIdentChar (char : Char) : Bool := isIdentStart char || isDigitChar char
def isSymbolChar (char : Char) : Bool := symbolChars.contains char

/-- The longest prefix satisfying `test`, and the remainder. -/
def spanWhile (test : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | char :: rest =>
      if test char then
        let (taken, remaining) := spanWhile test rest
        (char :: taken, remaining)
      else ([], char :: rest)

/-- Each step consumes at least one character, so `chars.length + 1` steps
are enough. -/
def lexWith : Nat → List Char → Option (List Token)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, char :: rest =>
      if isBlank char then lexWith fuel rest
      else if isIdentStart char then
        let (more, after) := spanWhile isIdentChar rest
        (Token.ident (String.ofList (char :: more)) :: ·) <$> lexWith fuel after
      else if isDigitChar char then
        let (more, after) := spanWhile isDigitChar rest
        (Token.number (Nat.ofDigitChars 10 (char :: more) 0) :: ·) <$> lexWith fuel after
      else if char = '=' then
        if rest.head? = some '=' then (Token.equalEqual :: ·) <$> lexWith fuel rest.tail
        else (Token.symbol '=' :: ·) <$> lexWith fuel rest
      else if isSymbolChar char then (Token.symbol char :: ·) <$> lexWith fuel rest
      else none

def lex (chars : List Char) : Option (List Token) := lexWith (chars.length + 1) chars

/-! ### Printed pieces

A printer emits tokens and blanks. The lexer recovers exactly the tokens when
no two word-like tokens touch and no `=` is directly followed by `=`. -/

inductive Piece where
  | token (token : Token)
  | blank (char : Char)
  deriving Repr, DecidableEq

def Token.chars : Token → List Char
  | .ident text => text.toList
  | .number value => Nat.toDigits 10 value
  | .symbol char => [char]
  | .equalEqual => ['=', '=']

def Piece.chars : Piece → List Char
  | .token value => value.chars
  | .blank char => [char]

def render : List Piece → List Char
  | [] => []
  | piece :: rest => piece.chars ++ render rest

def tokensOf : List Piece → List Token
  | [] => []
  | .token value :: rest => value :: tokensOf rest
  | .blank _ :: rest => tokensOf rest

/-- A lexically valid identifier spelling. -/
def ValidIdentifier (text : String) : Prop :=
  ∃ first rest, text.toList = first :: rest ∧ isIdentStart first = true ∧
    ∀ char ∈ rest, isIdentChar char = true

/-- Executable check for `ValidIdentifier`. -/
def validIdentifier (text : String) : Bool :=
  match text.toList with
  | first :: rest => isIdentStart first && rest.all isIdentChar
  | [] => false

theorem ValidIdentifier.of_check {text : String} (check : validIdentifier text = true) :
    ValidIdentifier text := by
  unfold validIdentifier at check
  split at check
  · rename_i first rest chars
    simp only [Bool.and_eq_true, List.all_eq_true] at check
    exact ⟨first, rest, chars, check.1, check.2⟩
  · cases check

def Piece.Valid : Piece → Prop
  | .token (.ident text) => ValidIdentifier text
  | .token (.number _) => True
  | .token (.symbol char) => isSymbolChar char = true ∨ char = '='
  | .token .equalEqual => True
  | .blank char => isBlank char = true

def Piece.wordLike : Piece → Bool
  | .token (.ident _) | .token (.number _) => true
  | _ => false

def Piece.startsWithEqual : Piece → Bool
  | .token .equalEqual => true
  | .token (.symbol char) => char == '='
  | _ => false

def Compatible (first second : Piece) : Prop :=
  ¬ (first.wordLike = true ∧ second.wordLike = true) ∧
    ¬ (first = .token (.symbol '=') ∧ second.startsWithEqual = true)

def Separated : List Piece → Prop
  | [] => True
  | [piece] => piece.Valid
  | first :: second :: rest => first.Valid ∧ Compatible first second ∧ Separated (second :: rest)

/-! ### Character classes -/

theorem blank_classes {char : Char} (blank : isBlank char = true) :
    isIdentChar char = false ∧ isIdentStart char = false ∧ isDigitChar char = false ∧
      char ≠ '=' := by
  simp only [isBlank, blankChars, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at blank
  rcases blank with rfl | rfl <;> decide

theorem symbol_classes {char : Char} (symbol : isSymbolChar char = true) :
    isBlank char = false ∧ isIdentChar char = false ∧ isIdentStart char = false ∧
      isDigitChar char = false ∧ char ≠ '=' := by
  have mem : char ∈ symbolChars := List.elem_iff.mp symbol
  simp only [symbolChars, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> decide

theorem identStart_classes {char : Char} (start : isIdentStart char = true) :
    isBlank char = false ∧ isIdentChar char = true := by
  have mem : char ∈ identifierStarts := List.elem_iff.mp start
  refine ⟨?_, by simp [isIdentChar, start]⟩
  have all : ∀ start ∈ identifierStarts, isBlank start = false := by decide
  exact all char mem

theorem digit_classes {char : Char} (digit : isDigitChar char = true) :
    isBlank char = false ∧ isIdentStart char = false ∧ isIdentChar char = true := by
  have mem : char ∈ decimalDigits := List.elem_iff.mp digit
  have all : ∀ digit ∈ decimalDigits, isBlank digit = false ∧ isIdentStart digit = false := by
    decide
  exact ⟨(all char mem).1, (all char mem).2, by simp [isIdentChar, digit]⟩

theorem equal_classes : isBlank '=' = false ∧ isIdentStart '=' = false ∧
    isDigitChar '=' = false ∧ isIdentChar '=' = false := by
  decide

theorem digitChar_mem {value : Nat} (small : value < 10) : Nat.digitChar value ∈ decimalDigits := by
  have all : ∀ value, value < 10 → Nat.digitChar value ∈ decimalDigits := by decide
  exact all value small

theorem toDigits_mem {value : Nat} {char : Char} (mem : char ∈ Nat.toDigits 10 value) :
    isDigitChar char = true := by
  induction value using Nat.strongRecOn with
  | ind value ih =>
      rw [Nat.toDigits_eq_if (by decide)] at mem
      split at mem
      · rename_i small
        simp only [List.mem_singleton] at mem
        subst mem
        exact List.elem_iff.mpr (digitChar_mem small)
      · rename_i large
        rcases List.mem_append.mp mem with mem | mem
        · exact ih (value / 10) (Nat.div_lt_self (by omega) (by decide)) mem
        · simp only [List.mem_singleton] at mem
          subst mem
          exact List.elem_iff.mpr (digitChar_mem (Nat.mod_lt _ (by decide)))

/-! ### Lexing printed pieces -/

theorem spanWhile_append {test : Char → Bool} {taken rest : List Char}
    (all : ∀ char ∈ taken, test char = true)
    (stops : ∀ char ∈ rest.head?, test char = false) :
    spanWhile test (taken ++ rest) = (taken, rest) := by
  induction taken with
  | nil =>
      cases rest with
      | nil => rfl
      | cons char tail =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq'] at stops
          simp [spanWhile, stops]
  | cons char taken ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at all
      simp [spanWhile, all.1, ih all.2]

theorem render_append (first second : List Piece) :
    render (first ++ second) = render first ++ render second := by
  induction first with
  | nil => rfl
  | cons piece rest ih => simp [render, ih, List.append_assoc]

theorem tokensOf_append (first second : List Piece) :
    tokensOf (first ++ second) = tokensOf first ++ tokensOf second := by
  induction first with
  | nil => rfl
  | cons piece rest ih =>
      cases piece with
      | token token => simp [tokensOf, ih]
      | blank char => simp [tokensOf, ih]

theorem Separated.tail {piece : Piece} {rest : List Piece} (separated : Separated (piece :: rest)) :
    Separated rest := by
  cases rest with
  | nil => trivial
  | cons second rest => exact separated.2.2

theorem Separated.head {piece : Piece} {rest : List Piece} (separated : Separated (piece :: rest)) :
    piece.Valid := by
  cases rest with
  | nil => exact separated
  | cons second rest => exact separated.1

theorem Piece.chars_cons {piece : Piece} (valid : piece.Valid) :
    ∃ first rest, piece.chars = first :: rest := by
  cases piece with
  | blank char => exact ⟨char, [], rfl⟩
  | token value =>
      cases value with
      | ident text =>
          obtain ⟨first, rest, chars, _⟩ := valid
          exact ⟨first, rest, chars⟩
      | number value =>
          exact List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (b := 10) (n := value))
      | symbol char => exact ⟨char, [], rfl⟩
      | equalEqual => exact ⟨'=', ['='], rfl⟩

theorem render_cons {piece : Piece} {rest : List Piece} {first : Char} {more : List Char}
    (chars : piece.chars = first :: more) :
    render (piece :: rest) = first :: (more ++ render rest) := by
  simp only [render, chars, List.cons_append]

/-- The first character of a piece that is not word-like. -/
theorem nonword_first {piece : Piece} (valid : piece.Valid) (notWord : piece.wordLike = false)
    {first : Char} {more : List Char} (chars : piece.chars = first :: more) :
    isIdentChar first = false ∧ isDigitChar first = false := by
  cases piece with
  | blank char =>
      simp only [Piece.chars] at chars
      cases chars
      have classes := blank_classes valid
      exact ⟨classes.1, classes.2.2.1⟩
  | token value =>
      cases value with
      | ident text => cases notWord
      | number value => cases notWord
      | symbol char =>
          simp only [Piece.chars, Token.chars] at chars
          cases chars
          rcases valid with valid | rfl
          · have classes := symbol_classes valid
            exact ⟨classes.2.1, classes.2.2.2.1⟩
          · exact ⟨equal_classes.2.2.2, equal_classes.2.2.1⟩
      | equalEqual =>
          simp only [Piece.chars, Token.chars] at chars
          cases chars
          exact ⟨equal_classes.2.2.2, equal_classes.2.2.1⟩

/-- The first character of a piece that does not start with `=`. -/
theorem not_equal_first {piece : Piece} (valid : piece.Valid)
    (notEqual : piece.startsWithEqual = false) {first : Char} {more : List Char}
    (chars : piece.chars = first :: more) : first ≠ '=' := by
  cases piece with
  | blank char =>
      simp only [Piece.chars] at chars
      cases chars
      exact (blank_classes valid).2.2.2
  | token value =>
      cases value with
      | ident text =>
          obtain ⟨start, rest, textChars, startClass, _⟩ := valid
          simp only [Piece.chars, Token.chars, textChars] at chars
          cases chars
          intro same
          subst same
          exact absurd startClass (by rw [equal_classes.2.1]; decide)
      | number value =>
          have digit : isDigitChar first = true := by
            simp only [Piece.chars, Token.chars] at chars
            exact toDigits_mem (chars ▸ List.mem_cons_self)
          intro same
          subst same
          exact absurd digit (by rw [equal_classes.2.2.1]; decide)
      | symbol char =>
          simp only [Piece.chars, Token.chars] at chars
          cases chars
          intro same
          subst same
          cases notEqual
      | equalEqual => cases notEqual

/-- After a word-like piece, the next printed character cannot continue it. -/
theorem stops_after_word {piece : Piece} {rest : List Piece} (separated : Separated (piece :: rest))
    (word : piece.wordLike = true) :
    ∀ char ∈ (render rest).head?, isIdentChar char = false ∧ isDigitChar char = false := by
  intro char found
  cases rest with
  | nil => cases found
  | cons following tail =>
      have valid := (Separated.tail separated).head
      obtain ⟨first, more, chars⟩ := Piece.chars_cons valid
      rw [render_cons chars] at found
      cases found
      have notWord : following.wordLike = false := by
        cases followingWord : following.wordLike
        · rfl
        · exact absurd ⟨word, followingWord⟩ separated.2.1.1
      exact nonword_first valid notWord chars

/-- After an `=` symbol, the next printed character is not `=`. -/
theorem stops_after_equal {rest : List Piece}
    (separated : Separated (.token (.symbol '=') :: rest)) : (render rest).head? ≠ some '=' := by
  intro found
  cases rest with
  | nil => cases found
  | cons following tail =>
      have valid := (Separated.tail separated).head
      obtain ⟨first, more, chars⟩ := Piece.chars_cons valid
      rw [render_cons chars] at found
      cases found
      have notEqual : following.startsWithEqual = false := by
        cases starts : following.startsWithEqual
        · rfl
        · exact absurd ⟨rfl, starts⟩ separated.2.1.2
      exact not_equal_first valid notEqual chars rfl

/-- **Lexer correctness.** Separated pieces lex to exactly their tokens. -/
theorem lexWith_render : ∀ (pieces : List Piece) (fuel : Nat),
    Separated pieces → (render pieces).length < fuel →
    lexWith fuel (render pieces) = some (tokensOf pieces)
  | [], fuel, _, _ => by cases fuel <;> rfl
  | piece :: rest, fuel, separated, enough => by
      have restSeparated := Separated.tail separated
      have valid := Separated.head separated
      obtain ⟨first, more, chars⟩ := Piece.chars_cons valid
      rw [render_cons chars] at enough ⊢
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 :=
        ⟨fuel - 1, by simp only [List.length_cons] at enough; omega⟩
      have lengths : (render rest).length < fuel := by
        simp only [List.length_cons, List.length_append] at enough
        omega
      have recursive := lexWith_render rest fuel restSeparated lengths
      cases piece with
      | blank char =>
          simp only [Piece.chars] at chars
          cases chars
          have blank : isBlank first = true := valid
          simp only [List.nil_append, lexWith]
          rw [if_pos blank]
          exact recursive
      | token value =>
          cases value with
          | ident text =>
              obtain ⟨start, tail, textChars, startClass, all⟩ := valid
              simp only [Piece.chars, Token.chars, textChars] at chars
              cases chars
              have stops := fun char found => (stops_after_word separated rfl char found).1
              have span := spanWhile_append (test := isIdentChar) all stops
              have textEq : String.ofList (first :: more) = text := by
                rw [← textChars, String.ofList_toList]
              simp only [lexWith, (identStart_classes startClass).1, startClass, span, textEq,
                recursive, tokensOf, Bool.false_eq_true, if_false, if_true, Option.map_eq_map,
                Option.map_some]
          | number value =>
              simp only [Piece.chars, Token.chars] at chars
              have firstDigit : isDigitChar first = true :=
                toDigits_mem (chars ▸ List.mem_cons_self)
              have all : ∀ char ∈ more, isDigitChar char = true := fun char mem =>
                toDigits_mem (chars ▸ List.mem_cons_of_mem first mem)
              have stops := fun char found => (stops_after_word separated rfl char found).2
              have span := spanWhile_append (test := isDigitChar) all stops
              have numberEq : Nat.ofDigitChars 10 (first :: more) 0 = value := by
                rw [← chars]
                exact Nat.ofDigitChars_ten_toDigits
              have classes := digit_classes firstDigit
              simp only [lexWith, classes.1, classes.2.1, firstDigit, span, numberEq, recursive,
                tokensOf, Bool.false_eq_true, if_false, if_true, Option.map_eq_map,
                Option.map_some]
          | symbol char =>
              simp only [Piece.chars, Token.chars] at chars
              cases chars
              rcases valid with symbol | rfl
              · have classes := symbol_classes symbol
                simp only [List.nil_append, lexWith, classes.1, classes.2.2.1, classes.2.2.2.1,
                  classes.2.2.2.2, symbol, recursive, tokensOf, Bool.false_eq_true, if_false,
                  if_true, Option.map_eq_map, Option.map_some]
              · have notEqual := stops_after_equal separated
                simp only [List.nil_append, lexWith, equal_classes, notEqual, recursive,
                  tokensOf, Bool.false_eq_true, if_false, if_true, Option.map_eq_map,
                  Option.map_some]
          | equalEqual =>
              simp only [Piece.chars, Token.chars] at chars
              cases chars
              simp only [List.cons_append, List.nil_append, lexWith, equal_classes,
                List.head?_cons, List.tail_cons, recursive, tokensOf, Bool.false_eq_true,
                if_false, if_true, Option.map_eq_map, Option.map_some]

theorem lex_render {pieces : List Piece} (separated : Separated pieces) :
    lex (render pieces) = some (tokensOf pieces) :=
  lexWith_render pieces _ separated (Nat.lt_succ_self _)

end Solcore.Synthesis.Source.ScalarMeaning
