import Solcore.Synthesis.Source.ScalarMeaning.Syntax
import Solcore.Synthesis.Source.ScalarMeaning.Semantics

/-!
# Emitted source text

The lexer, printer and parser of the scalar fragment, and the meaning of a text. Main declarations:
`Token`, `Expr.print`, `parseSource`, `sourceCall`. Main theorem: `parseSource_print`.
-/

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.Lex
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
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.Parse
/-! Token grammar and recursive-descent parser for the source fragment.
Operator applications are fully parenthesized, a parenthesized pair has a
comma where an infix operator would be, a name followed by `(` is a call,
statement blocks end at `}` and function bodies end at `return`. `parseFile`
inverts the token printing of every file whose names are not reserved
words. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

/-- Words that cannot name contracts, methods, parameters or locals. -/
def reservedWords : List String :=
  ["let", "if", "else", "return", "true", "false", "Typedef", "rep", "uint256", "word", "bool",
    "import", "from", "contract", "function", "public", "returns", "match", "case", "inl", "inr"]

def isReserved (text : String) : Bool := reservedWords.contains text

def UnaryOp.token : UnaryOp → Token
  | .not => .symbol '!'
  | .bitNot => .symbol '~'

def BinaryOp.token : BinaryOp → Token
  | .add => .symbol '+'
  | .sub => .symbol '-'
  | .mul => .symbol '*'
  | .bitAnd => .symbol '&'
  | .bitOr => .symbol '|'
  | .bitXor => .symbol '^'
  | .eq => .equalEqual
  | .gt => .symbol '>'

/-- The tokens of a type annotation. -/
def LocalType.tokens : LocalType → List Token
  | .word => [.ident "word"]
  | .bool => [.ident "bool"]
  | .wordPair => [.symbol '(', .ident "word", .symbol ',', .ident "word", .symbol ')']
  | .wordSum =>
      [.ident "sum", .symbol '<', .ident "word", .symbol ',', .ident "word", .symbol '>']

def Expr.tokens : Expr → List Token
  | .name identifier => [.ident identifier]
  | .number value => [.number value]
  | .bool value => [.ident (if value then "true" else "false")]
  | .unary op operand => [.symbol '(', op.token] ++ operand.tokens ++ [.symbol ')']
  | .binary op left right =>
      [.symbol '('] ++ left.tokens ++ [op.token] ++ right.tokens ++ [.symbol ')']
  | .typedefRep operand =>
      [.ident "Typedef", .symbol '.', .ident "rep", .symbol '('] ++ operand.tokens ++
        [.symbol ')']
  | .uint256 operand => [.ident "uint256", .symbol '('] ++ operand.tokens ++ [.symbol ')']
  | .call1 callee first => [.ident callee, .symbol '('] ++ first.tokens ++ [.symbol ')']
  | .call2 callee first second =>
      [.ident callee, .symbol '('] ++ first.tokens ++ [.symbol ','] ++ second.tokens ++
        [.symbol ')']
  | .call3 callee first second third =>
      [.ident callee, .symbol '('] ++ first.tokens ++ [.symbol ','] ++ second.tokens ++
        [.symbol ','] ++ third.tokens ++ [.symbol ')']
  | .tuple first second =>
      [.symbol '('] ++ first.tokens ++ [.symbol ','] ++ second.tokens ++ [.symbol ')']
  | .inl payload => [.ident "inl", .symbol '('] ++ payload.tokens ++ [.symbol ')']
  | .inr payload => [.ident "inr", .symbol '('] ++ payload.tokens ++ [.symbol ')']

mutual

def Stmt.tokens : Stmt → List Token
  | .letDecl identifier type initializer =>
      [.ident "let", .ident identifier, .symbol ':'] ++ type.tokens ++ [.symbol '='] ++
        initializer.tokens ++ [.symbol ';']
  | .assign identifier value => [.ident identifier, .symbol '='] ++ value.tokens ++ [.symbol ';']
  | .ifElse condition thenBlock elseBlock =>
      [.ident "if", .symbol '('] ++ condition.tokens ++ [.symbol ')', .symbol '{'] ++
        Stmt.listTokens thenBlock ++ [.symbol '}', .ident "else", .symbol '{'] ++
        Stmt.listTokens elseBlock ++ [.symbol '}']
  | .matchPair scrutinee first second body =>
      [.ident "match", .symbol '('] ++ scrutinee.tokens ++
        [.symbol ')', .symbol '{', .ident "case", .symbol '(', .ident first, .symbol ',',
          .ident second, .symbol ')', .symbol '{'] ++
        Stmt.listTokens body ++ [.symbol '}', .symbol '}']
  | .matchSum scrutinee left leftBody right rightBody =>
      [.ident "match", .symbol '('] ++ scrutinee.tokens ++
        [.symbol ')', .symbol '{', .ident "case", .ident "inl", .symbol '(', .ident left,
          .symbol ')', .symbol '{'] ++
        Stmt.listTokens leftBody ++
        [.symbol '}', .ident "case", .ident "inr", .symbol '(', .ident right, .symbol ')',
          .symbol '{'] ++
        Stmt.listTokens rightBody ++ [.symbol '}', .symbol '}']

def Stmt.listTokens : List Stmt → List Token
  | [] => []
  | statement :: rest => statement.tokens ++ Stmt.listTokens rest

end

def parameterTokens : List String → List Token
  | [] => []
  | [parameter] => [.ident parameter, .symbol ':', .ident "uint256"]
  | parameter :: next :: rest =>
      [.ident parameter, .symbol ':', .ident "uint256", .symbol ','] ++
        parameterTokens (next :: rest)

/-- A file's first tokens: the `pragma solcore;` declaration that the pinned compiler requires
first in every file, then the imports of `std` and `std.dispatch`. -/
def importTokens : List Token :=
  [.ident "pragma", .ident "solcore", .symbol ';',
    .ident "import", .symbol '*', .ident "from", .ident "std", .symbol ';',
    .ident "import", .symbol '*', .ident "from", .ident "std", .symbol '.', .ident "dispatch",
    .symbol ';']

def aliasTokens : List (String × String) → List Token
  | [] => []
  | [alias] => [.ident alias.1, .ident "as", .ident alias.2]
  | alias :: next :: rest =>
      [.ident alias.1, .ident "as", .ident alias.2, .symbol ','] ++ aliasTokens (next :: rest)

def aliasImportTokens : List (String × String) → List Token
  | [] => []
  | alias :: rest =>
      [.ident "import", .symbol '{'] ++ aliasTokens (alias :: rest) ++
        [.symbol '}', .ident "from", .ident "std", .symbol '.', .ident "opcodes", .symbol ';']

def typedParameterTokens : List (String × LocalType) → List Token
  | [] => []
  | [parameter] => [.ident parameter.1, .symbol ':'] ++ parameter.2.tokens
  | parameter :: next :: rest =>
      [.ident parameter.1, .symbol ':'] ++ parameter.2.tokens ++ [.symbol ','] ++
        typedParameterTokens (next :: rest)

def FunctionDecl.tokens (function : FunctionDecl) : List Token :=
  [.ident "function", .ident function.name, .symbol '('] ++
    typedParameterTokens function.parameters ++
    [.symbol ')', .ident "returns", .symbol '('] ++ function.resultType.tokens ++
    [.symbol ')', .symbol '{'] ++
    Stmt.listTokens function.body ++ [.ident "return"] ++ function.result.tokens ++
    [.symbol ';', .symbol '}']

def signatureTokens : List Token :=
  [.symbol ')', .ident "public", .ident "returns", .symbol '(', .ident "uint256", .symbol ')',
    .symbol '{']

def SourceFile.tokens (file : SourceFile) : List Token :=
  importTokens ++ aliasImportTokens file.opcodeAliases ++
    file.functions.flatMap FunctionDecl.tokens ++
    [.ident "contract", .ident file.contract, .symbol '{', .ident "function",
      .ident file.method.name, .symbol '('] ++ parameterTokens file.method.parameters ++
    signatureTokens ++ Stmt.listTokens file.method.body ++ [.ident "return"] ++
    file.method.result.tokens ++ [.symbol ';', .symbol '}', .symbol '}']

/-! ### Parser -/

def expectTokens : List Token → List Token → Option (List Token)
  | [], rest => some rest
  | expected :: more, actual :: rest => if expected = actual then expectTokens more rest else none
  | _ :: _, [] => none

def parseName : List Token → Option (String × List Token)
  | .ident text :: rest => if isReserved text then none else some (text, rest)
  | _ => none

def parseUnaryOp? : Token → Option UnaryOp
  | .symbol char => if char = '!' then some .not else if char = '~' then some .bitNot else none
  | _ => none

def parseBinaryOp? : Token → Option BinaryOp
  | .symbol char =>
      if char = '+' then some .add
      else if char = '-' then some .sub
      else if char = '*' then some .mul
      else if char = '&' then some .bitAnd
      else if char = '|' then some .bitOr
      else if char = '^' then some .bitXor
      else if char = '>' then some .gt
      else none
  | .equalEqual => some .eq
  | _ => none

/-- A type annotation: `word`, `bool`, `(word, word)` or `sum<word, word>`. -/
def parseLocalType : List Token → Option (LocalType × List Token)
  | .ident text :: rest =>
      if text = "word" then some (.word, rest)
      else if text = "bool" then some (.bool, rest)
      else if text = "sum" then do
        let rest ← expectTokens
          [.symbol '<', .ident "word", .symbol ',', .ident "word", .symbol '>'] rest
        some (.wordSum, rest)
      else none
  | .symbol char :: rest =>
      if char = '(' then do
        let rest ← expectTokens [.ident "word", .symbol ',', .ident "word", .symbol ')'] rest
        some (.wordPair, rest)
      else none
  | _ => none

/-- Parse one expression; `fuel` bounds the nesting depth. -/
def parseExpr : Nat → List Token → Option (Expr × List Token)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, .number value :: rest => some (.number value, rest)
  | fuel + 1, .ident text :: rest =>
      if text = "true" then some (.bool true, rest)
      else if text = "false" then some (.bool false, rest)
      else if text = "Typedef" then do
        let rest ← expectTokens [.symbol '.', .ident "rep", .symbol '('] rest
        let (operand, rest) ← parseExpr fuel rest
        let rest ← expectTokens [.symbol ')'] rest
        some (.typedefRep operand, rest)
      else if text = "uint256" then do
        let rest ← expectTokens [.symbol '('] rest
        let (operand, rest) ← parseExpr fuel rest
        let rest ← expectTokens [.symbol ')'] rest
        some (.uint256 operand, rest)
      else if text = "inl" then do
        let rest ← expectTokens [.symbol '('] rest
        let (payload, rest) ← parseExpr fuel rest
        let rest ← expectTokens [.symbol ')'] rest
        some (.inl payload, rest)
      else if text = "inr" then do
        let rest ← expectTokens [.symbol '('] rest
        let (payload, rest) ← parseExpr fuel rest
        let rest ← expectTokens [.symbol ')'] rest
        some (.inr payload, rest)
      else if isReserved text then none
      else if rest.head? = some (.symbol '(') then do
        let (first, rest) ← parseExpr fuel rest.tail
        match rest with
        | .symbol ')' :: rest => some (.call1 text first, rest)
        | .symbol ',' :: rest => do
            let (second, rest) ← parseExpr fuel rest
            match rest with
            | .symbol ')' :: rest => some (.call2 text first second, rest)
            | .symbol ',' :: rest => do
                let (third, rest) ← parseExpr fuel rest
                let rest ← expectTokens [.symbol ')'] rest
                some (.call3 text first second third, rest)
            | _ => none
        | _ => none
      else some (.name text, rest)
  | fuel + 1, .symbol char :: rest =>
      if char = '(' then
        match rest with
        | [] => none
        | next :: afterNext =>
            match parseUnaryOp? next with
            | some op => do
                let (operand, rest) ← parseExpr fuel afterNext
                let rest ← expectTokens [.symbol ')'] rest
                some (.unary op operand, rest)
            | none => do
                let (left, rest) ← parseExpr fuel rest
                match rest with
                | [] => none
                | next :: rest =>
                    if next = .symbol ',' then do
                      let (right, rest) ← parseExpr fuel rest
                      let rest ← expectTokens [.symbol ')'] rest
                      some (.tuple left right, rest)
                    else do
                      let op ← parseBinaryOp? next
                      let (right, rest) ← parseExpr fuel rest
                      let rest ← expectTokens [.symbol ')'] rest
                      some (.binary op left right, rest)
      else none
  | _ + 1, .equalEqual :: _ => none

/-- A statement list ends before `}` or `return`. -/
def blockEnds : List Token → Bool
  | .symbol char :: _ => char == '}'
  | .ident text :: _ => text == "return"
  | _ => false

mutual

def parseStmt : Nat → List Token → Option (Stmt × List Token)
  | 0, _ => none
  | fuel + 1, tokens =>
      match tokens with
      | .ident text :: rest =>
          if text = "let" then do
            let (identifier, rest) ← parseName rest
            let rest ← expectTokens [.symbol ':'] rest
            let (type, rest) ← parseLocalType rest
            let rest ← expectTokens [.symbol '='] rest
            let (initializer, rest) ← parseExpr fuel rest
            let rest ← expectTokens [.symbol ';'] rest
            some (.letDecl identifier type initializer, rest)
          else if text = "if" then do
            let rest ← expectTokens [.symbol '('] rest
            let (condition, rest) ← parseExpr fuel rest
            let rest ← expectTokens [.symbol ')', .symbol '{'] rest
            let (thenBlock, rest) ← parseStmts fuel rest
            let rest ← expectTokens [.symbol '}', .ident "else", .symbol '{'] rest
            let (elseBlock, rest) ← parseStmts fuel rest
            let rest ← expectTokens [.symbol '}'] rest
            some (.ifElse condition thenBlock elseBlock, rest)
          else if text = "match" then do
            let rest ← expectTokens [.symbol '('] rest
            let (scrutinee, rest) ← parseExpr fuel rest
            let rest ← expectTokens [.symbol ')', .symbol '{', .ident "case"] rest
            if rest.head? = some (.symbol '(') then do
              let (first, rest) ← parseName rest.tail
              let rest ← expectTokens [.symbol ','] rest
              let (second, rest) ← parseName rest
              let rest ← expectTokens [.symbol ')', .symbol '{'] rest
              let (body, rest) ← parseStmts fuel rest
              let rest ← expectTokens [.symbol '}', .symbol '}'] rest
              some (.matchPair scrutinee first second body, rest)
            else do
              let rest ← expectTokens [.ident "inl", .symbol '('] rest
              let (left, rest) ← parseName rest
              let rest ← expectTokens [.symbol ')', .symbol '{'] rest
              let (leftBody, rest) ← parseStmts fuel rest
              let rest ← expectTokens
                [.symbol '}', .ident "case", .ident "inr", .symbol '('] rest
              let (right, rest) ← parseName rest
              let rest ← expectTokens [.symbol ')', .symbol '{'] rest
              let (rightBody, rest) ← parseStmts fuel rest
              let rest ← expectTokens [.symbol '}', .symbol '}'] rest
              some (.matchSum scrutinee left leftBody right rightBody, rest)
          else if isReserved text then none
          else do
            let rest ← expectTokens [.symbol '='] rest
            let (value, rest) ← parseExpr fuel rest
            let rest ← expectTokens [.symbol ';'] rest
            some (.assign text value, rest)
      | _ => none

def parseStmts : Nat → List Token → Option (List Stmt × List Token)
  | 0, _ => none
  | fuel + 1, tokens =>
      if blockEnds tokens then some ([], tokens)
      else do
        let (statement, rest) ← parseStmt fuel tokens
        let (statements, rest) ← parseStmts fuel rest
        some (statement :: statements, rest)

end

/-- `name: uint256` parameters separated by commas, up to the closing
parenthesis. -/
def parseParameterList : Nat → List Token → Option (List String × List Token)
  | 0, _ => none
  | fuel + 1, tokens => do
      let (parameter, rest) ← parseName tokens
      let rest ← expectTokens [.symbol ':', .ident "uint256"] rest
      match rest with
      | .symbol ',' :: rest => do
          let (parameters, rest) ← parseParameterList fuel rest
          some (parameter :: parameters, rest)
      | _ => some ([parameter], rest)

def parseParameters (tokens : List Token) : Option (List String × List Token) :=
  if tokens.head? = some (.symbol ')') then some ([], tokens)
  else parseParameterList (tokens.length + 1) tokens

/-- `opcode as alias` pairs separated by commas, up to the closing brace. -/
def parseAliasList : Nat → List Token → Option (List (String × String) × List Token)
  | 0, _ => none
  | fuel + 1, .ident opcode :: .ident keyword :: .ident alias :: rest =>
      if keyword = "as" then
        if rest.head? = some (.symbol ',') then do
          let (aliases, rest) ← parseAliasList fuel rest.tail
          some ((opcode, alias) :: aliases, rest)
        else some ([(opcode, alias)], rest)
      else none
  | _ + 1, _ => none

/-- An optional `import { opcode as alias, ... } from std.opcodes;`. -/
def parseAliasImport (tokens : List Token) : Option (List (String × String) × List Token) :=
  if tokens.head? = some (.ident "import") then do
    let rest ← expectTokens [.ident "import", .symbol '{'] tokens
    let (aliases, rest) ← parseAliasList (rest.length + 1) rest
    let rest ← expectTokens
      [.symbol '}', .ident "from", .ident "std", .symbol '.', .ident "opcodes", .symbol ';'] rest
    some (aliases, rest)
  else some ([], tokens)

/-- `name: type` parameters separated by commas, up to the closing
parenthesis. -/
def parseTypedParameterList :
    Nat → List Token → Option (List (String × LocalType) × List Token)
  | 0, _ => none
  | fuel + 1, tokens => do
      let (parameter, rest) ← parseName tokens
      let rest ← expectTokens [.symbol ':'] rest
      let (type, rest) ← parseLocalType rest
      if rest.head? = some (.symbol ',') then do
        let (parameters, rest) ← parseTypedParameterList fuel rest.tail
        some ((parameter, type) :: parameters, rest)
      else some ([(parameter, type)], rest)

def parseTypedParameters (tokens : List Token) :
    Option (List (String × LocalType) × List Token) :=
  if tokens.head? = some (.symbol ')') then some ([], tokens)
  else parseTypedParameterList (tokens.length + 1) tokens

def parseFunction (fuel : Nat) (tokens : List Token) : Option (FunctionDecl × List Token) := do
  let rest ← expectTokens [.ident "function"] tokens
  let (name, rest) ← parseName rest
  let rest ← expectTokens [.symbol '('] rest
  let (parameters, rest) ← parseTypedParameters rest
  let rest ← expectTokens [.symbol ')', .ident "returns", .symbol '('] rest
  let (resultType, rest) ← parseLocalType rest
  let rest ← expectTokens [.symbol ')', .symbol '{'] rest
  let (body, rest) ← parseStmts fuel rest
  let rest ← expectTokens [.ident "return"] rest
  let (result, rest) ← parseExpr fuel rest
  let rest ← expectTokens [.symbol ';', .symbol '}'] rest
  some (⟨name, parameters, resultType, body, result⟩, rest)

/-- Free functions up to the contract; `count` bounds their number. -/
def parseFunctions : Nat → Nat → List Token → Option (List FunctionDecl × List Token)
  | 0, _, _ => none
  | count + 1, fuel, tokens =>
      if tokens.head? = some (.ident "function") then do
        let (function, rest) ← parseFunction fuel tokens
        let (functions, rest) ← parseFunctions count fuel rest
        some (function :: functions, rest)
      else some ([], tokens)

def parseFileWith (fuel : Nat) (tokens : List Token) : Option SourceFile := do
  let rest ← expectTokens importTokens tokens
  let (opcodeAliases, rest) ← parseAliasImport rest
  let (functions, rest) ← parseFunctions (tokens.length + 1) fuel rest
  let rest ← expectTokens [.ident "contract"] rest
  let (contract, rest) ← parseName rest
  let rest ← expectTokens [.symbol '{', .ident "function"] rest
  let (method, rest) ← parseName rest
  let rest ← expectTokens [.symbol '('] rest
  let (parameters, rest) ← parseParameters rest
  let rest ← expectTokens signatureTokens rest
  let (body, rest) ← parseStmts fuel rest
  let rest ← expectTokens [.ident "return"] rest
  let (result, rest) ← parseExpr fuel rest
  let rest ← expectTokens [.symbol ';', .symbol '}', .symbol '}'] rest
  if rest = [] then some ⟨opcodeAliases, functions, contract, ⟨method, parameters, body, result⟩⟩
  else none

/-- Parse a complete token stream; one more than its length bounds nesting. -/
def parseFile (tokens : List Token) : Option SourceFile :=
  parseFileWith (tokens.length + 1) tokens

/-! ### Sizes -/

def Expr.size : Expr → Nat
  | .name _ | .number _ | .bool _ => 1
  | .unary _ operand | .typedefRep operand | .uint256 operand => operand.size + 1
  | .binary _ left right => left.size + right.size + 1
  | .call1 _ first => first.size + 1
  | .call2 _ first second => first.size + second.size + 1
  | .call3 _ first second third => first.size + second.size + third.size + 1
  | .tuple first second => first.size + second.size + 1
  | .inl payload | .inr payload => payload.size + 1

mutual

def Stmt.size : Stmt → Nat
  | .letDecl _ _ initializer => initializer.size + 1
  | .assign _ value => value.size + 1
  | .ifElse condition thenBlock elseBlock =>
      condition.size + Stmt.listSize thenBlock + Stmt.listSize elseBlock + 1
  | .matchPair scrutinee _ _ body => scrutinee.size + Stmt.listSize body + 1
  | .matchSum scrutinee _ leftBody _ rightBody =>
      scrutinee.size + Stmt.listSize leftBody + Stmt.listSize rightBody + 1

def Stmt.listSize : List Stmt → Nat
  | [] => 0
  | statement :: rest => statement.size + Stmt.listSize rest + 1

end

/-! ### Round trip -/

theorem expectTokens_append (expected rest : List Token) :
    expectTokens expected (expected ++ rest) = some rest := by
  induction expected with
  | nil => rfl
  | cons token more ih => simp [expectTokens, ih]

theorem parseName_cons {text : String} (notReserved : isReserved text = false)
    (rest : List Token) : parseName (.ident text :: rest) = some (text, rest) := by
  simp [parseName, notReserved]

theorem UnaryOp.parse_token (op : UnaryOp) : parseUnaryOp? op.token = some op := by
  cases op <;> rfl

theorem BinaryOp.parse_token (op : BinaryOp) : parseBinaryOp? op.token = some op := by
  cases op <;> rfl

theorem BinaryOp.token_ne_open (op : BinaryOp) : op.token ≠ .symbol '(' := by
  cases op <;> decide

theorem BinaryOp.token_ne_comma (op : BinaryOp) : op.token ≠ .symbol ',' := by
  cases op <;> decide

theorem LocalType.parse_tokens (type : LocalType) (rest : List Token) :
    parseLocalType (type.tokens ++ rest) = some (type, rest) := by
  cases type <;> simp [LocalType.tokens, parseLocalType, expectTokens]

theorem LocalType.tokens_head (type : LocalType) :
    ∃ first more, type.tokens = first :: more := by
  cases type <;> exact ⟨_, _, rfl⟩

/-- Every name in the expression is a non-reserved word. -/
def Expr.NamesOk (expression : Expr) : Prop :=
  ∀ name ∈ expression.identifiers, isReserved name = false

theorem not_reserved_names {text : String} (notReserved : isReserved text = false) :
    text ≠ "true" ∧ text ≠ "false" ∧ text ≠ "Typedef" ∧ text ≠ "uint256" ∧ text ≠ "inl" ∧
      text ≠ "inr" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro same <;> subst same <;>
    simp [isReserved, reservedWords] at notReserved

theorem Expr.tokens_head (expression : Expr) :
    ∃ first rest, expression.tokens = first :: rest ∧ parseUnaryOp? first = none := by
  cases expression with
  | name identifier => exact ⟨_, _, rfl, rfl⟩
  | number value => exact ⟨_, _, rfl, rfl⟩
  | bool value => exact ⟨_, _, rfl, rfl⟩
  | unary op operand => exact ⟨_, _, rfl, rfl⟩
  | binary op left right => exact ⟨_, _, rfl, rfl⟩
  | typedefRep operand => exact ⟨_, _, rfl, rfl⟩
  | uint256 operand => exact ⟨_, _, rfl, rfl⟩
  | call1 callee first => exact ⟨_, _, rfl, rfl⟩
  | call2 callee first second => exact ⟨_, _, rfl, rfl⟩
  | call3 callee first second third => exact ⟨_, _, rfl, rfl⟩
  | tuple first second => exact ⟨_, _, rfl, rfl⟩
  | inl payload => exact ⟨_, _, rfl, rfl⟩
  | inr payload => exact ⟨_, _, rfl, rfl⟩

/-- Expression round trip. The next token must not be `(`, which would turn
a final name into a call; every printed context satisfies this. -/
theorem parseExpr_tokens : ∀ (expression : Expr) (fuel : Nat) (rest : List Token),
    expression.NamesOk → expression.size < fuel → rest.head? ≠ some (.symbol '(') →
    parseExpr fuel (expression.tokens ++ rest) = some (expression, rest)
  | .name identifier, fuel + 1, rest, names, _, notOpen => by
      have notReserved : isReserved identifier = false :=
        names identifier (by simp [Expr.identifiers])
      obtain ⟨notTrue, notFalse, notTypedef, notUint, notInl, notInr⟩ :=
        not_reserved_names notReserved
      simp [Expr.tokens, parseExpr, notTrue, notFalse, notTypedef, notUint, notInl, notInr,
        notReserved, notOpen]
  | .number value, fuel + 1, rest, _, _, _ => by simp [Expr.tokens, parseExpr]
  | .bool value, fuel + 1, rest, _, _, _ => by cases value <;> simp [Expr.tokens, parseExpr]
  | .unary op operand, fuel + 1, rest, names, enough, _ => by
      have operandParse := parseExpr_tokens operand fuel ([.symbol ')'] ++ rest)
        (fun name mem => names name (by simpa [Expr.identifiers] using mem))
        (by simp only [Expr.size] at enough; omega) (by simp)
      simp only [Expr.tokens, List.append_assoc, List.cons_append,
        List.nil_append] at operandParse ⊢
      simp [parseExpr, UnaryOp.parse_token, operandParse, expectTokens]
  | .binary op left right, fuel + 1, rest, names, enough, _ => by
      have rightParse := parseExpr_tokens right fuel ([.symbol ')'] ++ rest)
        (fun name mem => names name (by simp [Expr.identifiers, mem]))
        (by simp only [Expr.size] at enough; omega) (by simp)
      have leftParse := parseExpr_tokens left fuel
        ([op.token] ++ right.tokens ++ [.symbol ')'] ++ rest)
        (fun name mem => names name (by simp [Expr.identifiers, mem]))
        (by simp only [Expr.size] at enough; omega) (by simpa using op.token_ne_open)
      obtain ⟨first, tail, head, notUnary⟩ := Expr.tokens_head left
      simp only [List.append_assoc, List.cons_append, List.nil_append] at leftParse rightParse
      rw [head, List.cons_append] at leftParse
      simp only [Expr.tokens, head, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseExpr, notUnary, leftParse, BinaryOp.parse_token, BinaryOp.token_ne_comma,
        rightParse, expectTokens]
  | .typedefRep operand, fuel + 1, rest, names, enough, _ => by
      have operandParse := parseExpr_tokens operand fuel ([.symbol ')'] ++ rest)
        (fun name mem => names name (by simpa [Expr.identifiers] using mem))
        (by simp only [Expr.size] at enough; omega) (by simp)
      simp only [Expr.tokens, List.append_assoc, List.cons_append,
        List.nil_append] at operandParse ⊢
      simp [parseExpr, operandParse, expectTokens]
  | .uint256 operand, fuel + 1, rest, names, enough, _ => by
      have operandParse := parseExpr_tokens operand fuel ([.symbol ')'] ++ rest)
        (fun name mem => names name (by simpa [Expr.identifiers] using mem))
        (by simp only [Expr.size] at enough; omega) (by simp)
      simp only [Expr.tokens, List.append_assoc, List.cons_append,
        List.nil_append] at operandParse ⊢
      simp [parseExpr, operandParse, expectTokens]
  | .call1 callee first, fuel + 1, rest, names, enough, _ => by
      have calleeOk : isReserved callee = false := names callee (by simp [Expr.identifiers])
      obtain ⟨notTrue, notFalse, notTypedef, notUint, notInl, notInr⟩ :=
        not_reserved_names calleeOk
      have firstParse := parseExpr_tokens first fuel ([.symbol ')'] ++ rest)
        (fun name mem => names name (by simp [Expr.identifiers, mem]))
        (by simp only [Expr.size] at enough; omega) (by simp)
      simp only [List.cons_append, List.nil_append] at firstParse
      simp only [Expr.tokens, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseExpr, notTrue, notFalse, notTypedef, notUint, notInl, notInr, calleeOk,
        firstParse]
  | .call2 callee first second, fuel + 1, rest, names, enough, _ => by
      have calleeOk : isReserved callee = false := names callee (by simp [Expr.identifiers])
      obtain ⟨notTrue, notFalse, notTypedef, notUint, notInl, notInr⟩ :=
        not_reserved_names calleeOk
      have secondParse := parseExpr_tokens second fuel ([.symbol ')'] ++ rest)
        (fun name mem => names name (by simp [Expr.identifiers, mem]))
        (by simp only [Expr.size] at enough; omega) (by simp)
      have firstParse := parseExpr_tokens first fuel
        ([.symbol ','] ++ second.tokens ++ [.symbol ')'] ++ rest)
        (fun name mem => names name (by simp [Expr.identifiers, mem]))
        (by simp only [Expr.size] at enough; omega) (by simp)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at firstParse
      simp only [List.cons_append, List.nil_append] at secondParse
      simp only [Expr.tokens, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseExpr, notTrue, notFalse, notTypedef, notUint, notInl, notInr, calleeOk,
        firstParse, secondParse]
  | .call3 callee first second third, fuel + 1, rest, names, enough, _ => by
      have calleeOk : isReserved callee = false := names callee (by simp [Expr.identifiers])
      obtain ⟨notTrue, notFalse, notTypedef, notUint, notInl, notInr⟩ :=
        not_reserved_names calleeOk
      have thirdParse := parseExpr_tokens third fuel ([.symbol ')'] ++ rest)
        (fun name mem => names name (by simp [Expr.identifiers, mem]))
        (by simp only [Expr.size] at enough; omega) (by simp)
      have secondParse := parseExpr_tokens second fuel
        ([.symbol ','] ++ third.tokens ++ [.symbol ')'] ++ rest)
        (fun name mem => names name (by simp [Expr.identifiers, mem]))
        (by simp only [Expr.size] at enough; omega) (by simp)
      have firstParse := parseExpr_tokens first fuel
        ([.symbol ','] ++ second.tokens ++ [.symbol ','] ++ third.tokens ++ [.symbol ')'] ++
          rest)
        (fun name mem => names name (by simp [Expr.identifiers, mem]))
        (by simp only [Expr.size] at enough; omega) (by simp)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at firstParse
      simp only [List.append_assoc, List.cons_append, List.nil_append] at secondParse
      simp only [List.cons_append, List.nil_append] at thirdParse
      simp only [Expr.tokens, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseExpr, notTrue, notFalse, notTypedef, notUint, notInl, notInr, calleeOk,
        firstParse, secondParse, thirdParse, expectTokens]
  | .tuple first second, fuel + 1, rest, names, enough, _ => by
      have secondParse := parseExpr_tokens second fuel ([.symbol ')'] ++ rest)
        (fun name mem => names name (by simp [Expr.identifiers, mem]))
        (by simp only [Expr.size] at enough; omega) (by simp)
      have firstParse := parseExpr_tokens first fuel
        ([.symbol ','] ++ second.tokens ++ [.symbol ')'] ++ rest)
        (fun name mem => names name (by simp [Expr.identifiers, mem]))
        (by simp only [Expr.size] at enough; omega) (by simp)
      obtain ⟨head, tail, headEq, notUnary⟩ := Expr.tokens_head first
      simp only [List.append_assoc, List.cons_append, List.nil_append] at firstParse secondParse
      rw [headEq, List.cons_append] at firstParse
      simp only [Expr.tokens, headEq, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseExpr, notUnary, firstParse, secondParse, expectTokens]
  | .inl payload, fuel + 1, rest, names, enough, _ => by
      have payloadParse := parseExpr_tokens payload fuel ([.symbol ')'] ++ rest)
        (fun name mem => names name (by simpa [Expr.identifiers] using mem))
        (by simp only [Expr.size] at enough; omega) (by simp)
      simp only [Expr.tokens, List.append_assoc, List.cons_append,
        List.nil_append] at payloadParse ⊢
      simp [parseExpr, payloadParse, expectTokens]
  | .inr payload, fuel + 1, rest, names, enough, _ => by
      have payloadParse := parseExpr_tokens payload fuel ([.symbol ')'] ++ rest)
        (fun name mem => names name (by simpa [Expr.identifiers] using mem))
        (by simp only [Expr.size] at enough; omega) (by simp)
      simp only [Expr.tokens, List.append_assoc, List.cons_append,
        List.nil_append] at payloadParse ⊢
      simp [parseExpr, payloadParse, expectTokens]
  | _, 0, _, _, enough, _ => absurd enough (Nat.not_lt_zero _)

def Stmt.NamesOk (statement : Stmt) : Prop :=
  ∀ name ∈ statement.identifiers, isReserved name = false

def Stmt.ListNamesOk (statements : List Stmt) : Prop :=
  ∀ name ∈ Stmt.listIdentifiers statements, isReserved name = false

theorem not_reserved_ne {text : String} (notReserved : isReserved text = false) :
    text ≠ "let" ∧ text ≠ "if" ∧ text ≠ "return" ∧ text ≠ "match" := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro same <;> subst same <;>
    simp [isReserved, reservedWords] at notReserved

theorem Stmt.blockEnds_tokens (statement : Stmt) (names : statement.NamesOk)
    (rest : List Token) : blockEnds (statement.tokens ++ rest) = false := by
  cases statement with
  | letDecl identifier type initializer => rfl
  | assign identifier value =>
      have notReserved : isReserved identifier = false :=
        names identifier (by simp [Stmt.identifiers])
      have notReturn := (not_reserved_ne notReserved).2.2.1
      simp [Stmt.tokens, blockEnds, notReturn]
  | ifElse condition thenBlock elseBlock => rfl
  | matchPair scrutinee first second body => rfl
  | matchSum scrutinee left leftBody right rightBody => rfl

/-- Statement and statement-list round trips, by induction on the fuel. -/
theorem parseStmt_tokens_all (fuel : Nat) :
    (∀ (statement : Stmt) (rest : List Token), statement.NamesOk → statement.size < fuel →
      parseStmt fuel (statement.tokens ++ rest) = some (statement, rest)) ∧
    (∀ (statements : List Stmt) (rest : List Token), Stmt.ListNamesOk statements →
      Stmt.listSize statements < fuel → blockEnds rest = true →
      parseStmts fuel (Stmt.listTokens statements ++ rest) = some (statements, rest)) := by
  induction fuel with
  | zero =>
      exact ⟨fun _ _ _ enough => absurd enough (Nat.not_lt_zero _),
        fun _ _ _ enough => absurd enough (Nat.not_lt_zero _)⟩
  | succ fuel ih =>
      obtain ⟨statementIH, listIH⟩ := ih
      refine ⟨?_, ?_⟩
      · intro statement rest names enough
        cases statement with
        | letDecl identifier type initializer =>
            have notReserved : isReserved identifier = false :=
              names identifier (by simp [Stmt.identifiers])
            have initializerParse := parseExpr_tokens initializer fuel ([.symbol ';'] ++ rest)
              (fun name mem => names name (by simp [Stmt.identifiers, mem]))
              (by simp only [Stmt.size] at enough; omega) (by simp)
            simp only [Stmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
              at initializerParse ⊢
            simp [parseStmt, parseName_cons notReserved, expectTokens, LocalType.parse_tokens,
              initializerParse]
        | assign identifier value =>
            have notReserved : isReserved identifier = false :=
              names identifier (by simp [Stmt.identifiers])
            obtain ⟨notLet, notIf, _, notMatch⟩ := not_reserved_ne notReserved
            have valueParse := parseExpr_tokens value fuel ([.symbol ';'] ++ rest)
              (fun name mem => names name (by simp [Stmt.identifiers, mem]))
              (by simp only [Stmt.size] at enough; omega) (by simp)
            simp only [Stmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
              at valueParse ⊢
            simp [parseStmt, notLet, notIf, notMatch, notReserved, expectTokens, valueParse]
        | ifElse condition thenBlock elseBlock =>
            have elseParse := listIH elseBlock ([.symbol '}'] ++ rest)
              (fun name mem => names name (by simp [Stmt.identifiers, mem]))
              (by simp only [Stmt.size] at enough; omega) rfl
            have thenParse := listIH thenBlock
              ([.symbol '}', .ident "else", .symbol '{'] ++ Stmt.listTokens elseBlock ++
                [.symbol '}'] ++ rest)
              (fun name mem => names name (by simp [Stmt.identifiers, mem]))
              (by simp only [Stmt.size] at enough; omega) rfl
            have conditionParse := parseExpr_tokens condition fuel
              ([.symbol ')', .symbol '{'] ++ Stmt.listTokens thenBlock ++
                [.symbol '}', .ident "else", .symbol '{'] ++ Stmt.listTokens elseBlock ++
                [.symbol '}'] ++ rest)
              (fun name mem => names name (by simp [Stmt.identifiers, mem]))
              (by simp only [Stmt.size] at enough; omega) (by simp)
            simp only [List.cons_append, List.nil_append] at elseParse
            simp only [List.append_assoc, List.cons_append, List.nil_append] at thenParse
            simp only [List.append_assoc, List.cons_append, List.nil_append] at conditionParse
            simp only [Stmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
            simp [parseStmt, expectTokens, conditionParse, thenParse, elseParse]
        | matchPair scrutinee first second body =>
            have firstOk : isReserved first = false :=
              names first (by simp [Stmt.identifiers])
            have secondOk : isReserved second = false :=
              names second (by simp [Stmt.identifiers])
            have bodyParse := listIH body ([.symbol '}', .symbol '}'] ++ rest)
              (fun name mem => names name (by simp [Stmt.identifiers, mem]))
              (by simp only [Stmt.size] at enough; omega) rfl
            have scrutineeParse := parseExpr_tokens scrutinee fuel
              ([.symbol ')', .symbol '{', .ident "case", .symbol '(', .ident first, .symbol ',',
                .ident second, .symbol ')', .symbol '{'] ++ Stmt.listTokens body ++
                [.symbol '}', .symbol '}'] ++ rest)
              (fun name mem => names name (by simp [Stmt.identifiers, mem]))
              (by simp only [Stmt.size] at enough; omega) (by simp)
            simp only [List.cons_append, List.nil_append] at bodyParse
            simp only [List.append_assoc, List.cons_append, List.nil_append] at scrutineeParse
            simp only [Stmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
            simp [parseStmt, expectTokens, scrutineeParse, parseName_cons firstOk,
              parseName_cons secondOk, bodyParse]
        | matchSum scrutinee left leftBody right rightBody =>
            have leftOk : isReserved left = false :=
              names left (by simp [Stmt.identifiers])
            have rightOk : isReserved right = false :=
              names right (by simp [Stmt.identifiers])
            have rightParse := listIH rightBody ([.symbol '}', .symbol '}'] ++ rest)
              (fun name mem => names name (by simp [Stmt.identifiers, mem]))
              (by simp only [Stmt.size] at enough; omega) rfl
            have leftParse := listIH leftBody
              ([.symbol '}', .ident "case", .ident "inr", .symbol '(', .ident right, .symbol ')',
                .symbol '{'] ++ Stmt.listTokens rightBody ++ [.symbol '}', .symbol '}'] ++ rest)
              (fun name mem => names name (by simp [Stmt.identifiers, mem]))
              (by simp only [Stmt.size] at enough; omega) rfl
            have scrutineeParse := parseExpr_tokens scrutinee fuel
              ([.symbol ')', .symbol '{', .ident "case", .ident "inl", .symbol '(', .ident left,
                .symbol ')', .symbol '{'] ++ Stmt.listTokens leftBody ++
                [.symbol '}', .ident "case", .ident "inr", .symbol '(', .ident right, .symbol ')',
                  .symbol '{'] ++ Stmt.listTokens rightBody ++ [.symbol '}', .symbol '}'] ++ rest)
              (fun name mem => names name (by simp [Stmt.identifiers, mem]))
              (by simp only [Stmt.size] at enough; omega) (by simp)
            simp only [List.cons_append, List.nil_append] at rightParse
            simp only [List.append_assoc, List.cons_append, List.nil_append] at leftParse
            simp only [List.append_assoc, List.cons_append, List.nil_append] at scrutineeParse
            simp only [Stmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
            simp [parseStmt, expectTokens, scrutineeParse, parseName_cons leftOk,
              parseName_cons rightOk, leftParse, rightParse]
      · intro statements rest names enough ends
        cases statements with
        | nil => simp [Stmt.listTokens, parseStmts, ends]
        | cons statement tail =>
            have statementNames : statement.NamesOk := fun name mem =>
              names name (by simp [Stmt.listIdentifiers, mem])
            have tailParse := listIH tail rest
              (fun name mem => names name (by simp [Stmt.listIdentifiers, mem]))
              (by simp only [Stmt.listSize] at enough; omega) ends
            have statementParse := statementIH statement (Stmt.listTokens tail ++ rest)
              statementNames (by simp only [Stmt.listSize] at enough; omega)
            simp only [Stmt.listTokens, List.append_assoc]
            simp [parseStmts, Stmt.blockEnds_tokens statement statementNames, statementParse,
              tailParse]

theorem parseStmts_tokens {statements : List Stmt} {fuel : Nat} {rest : List Token}
    (names : Stmt.ListNamesOk statements) (enough : Stmt.listSize statements < fuel)
    (ends : blockEnds rest = true) :
    parseStmts fuel (Stmt.listTokens statements ++ rest) = some (statements, rest) :=
  (parseStmt_tokens_all fuel).2 statements rest names enough ends

theorem parseParameterList_tokens : ∀ (parameters : List String) (fuel : Nat) (rest : List Token),
    parameters ≠ [] → (∀ parameter ∈ parameters, isReserved parameter = false) →
    parameters.length ≤ fuel → rest.head? = some (.symbol ')') →
    parseParameterList fuel (parameterTokens parameters ++ rest) = some (parameters, rest)
  | [], _, _, nonempty, _, _, _ => absurd rfl nonempty
  | [parameter], fuel + 1, rest, _, names, _, closing => by
      have notReserved := names parameter (by simp)
      cases rest with
      | nil => simp at closing
      | cons first tail =>
          simp only [List.head?_cons, Option.some.injEq] at closing
          subst closing
          simp [parameterTokens, parseParameterList, parseName_cons notReserved, expectTokens]
  | parameter :: next :: more, fuel + 1, rest, _, names, enough, closing => by
      have notReserved := names parameter (by simp)
      have tailParse := parseParameterList_tokens (next :: more) fuel rest (by simp)
        (fun name mem => names name (List.mem_cons_of_mem _ mem))
        (by simp only [List.length_cons] at enough ⊢; omega) closing
      simp only [parameterTokens, List.cons_append, List.nil_append]
      simp [parseParameterList, parseName_cons notReserved, expectTokens, tailParse]
  | _ :: _, 0, _, _, _, enough, _ => absurd enough (by simp)

theorem parameterTokens_length : (parameters : List String) →
    parameters.length ≤ (parameterTokens parameters).length
  | [] => Nat.le_refl _
  | [_] => by simp [parameterTokens]
  | _ :: next :: more => by
      have := parameterTokens_length (next :: more)
      simp only [parameterTokens, List.length_append, List.length_cons] at this ⊢
      omega

theorem parseParameters_tokens (parameters : List String) (rest : List Token)
    (names : ∀ parameter ∈ parameters, isReserved parameter = false)
    (closing : rest.head? = some (.symbol ')')) :
    parseParameters (parameterTokens parameters ++ rest) = some (parameters, rest) := by
  cases parameters with
  | nil => simp [parameterTokens, parseParameters, closing]
  | cons parameter more =>
      have notClosing : (parameterTokens (parameter :: more) ++ rest).head? ≠
          some (.symbol ')') := by
        cases more <;> simp [parameterTokens]
      rw [parseParameters, if_neg notClosing]
      have := parameterTokens_length (parameter :: more)
      exact parseParameterList_tokens _ _ rest (by simp) names
        (by simp only [List.length_append]; omega) closing

theorem parseTypedParameterList_tokens :
    ∀ (parameters : List (String × LocalType)) (fuel : Nat) (rest : List Token),
    parameters ≠ [] → (∀ parameter ∈ parameters, isReserved parameter.1 = false) →
    parameters.length ≤ fuel → rest.head? = some (.symbol ')') →
    parseTypedParameterList fuel (typedParameterTokens parameters ++ rest) =
      some (parameters, rest)
  | [], _, _, nonempty, _, _, _ => absurd rfl nonempty
  | [parameter], fuel + 1, rest, _, names, _, closing => by
      have notReserved := names parameter (by simp)
      cases rest with
      | nil => simp at closing
      | cons first tail =>
          simp only [List.head?_cons, Option.some.injEq] at closing
          subst closing
          simp [typedParameterTokens, parseTypedParameterList, parseName_cons notReserved,
            expectTokens, LocalType.parse_tokens]
  | parameter :: next :: more, fuel + 1, rest, _, names, enough, closing => by
      have notReserved := names parameter (by simp)
      have tailParse := parseTypedParameterList_tokens (next :: more) fuel rest (by simp)
        (fun name mem => names name (List.mem_cons_of_mem _ mem))
        (by simp only [List.length_cons] at enough ⊢; omega) closing
      simp only [typedParameterTokens, List.cons_append, List.nil_append, List.append_assoc]
      simp [parseTypedParameterList, parseName_cons notReserved, expectTokens,
        LocalType.parse_tokens, tailParse]
  | _ :: _, 0, _, _, _, enough, _ => absurd enough (by simp)

theorem typedParameterTokens_length : (parameters : List (String × LocalType)) →
    parameters.length ≤ (typedParameterTokens parameters).length
  | [] => Nat.le_refl _
  | [_] => by simp [typedParameterTokens]
  | _ :: next :: more => by
      have := typedParameterTokens_length (next :: more)
      simp only [typedParameterTokens, List.length_append, List.length_cons,
        List.length_nil] at this ⊢
      omega

theorem parseTypedParameters_tokens (parameters : List (String × LocalType))
    (rest : List Token) (names : ∀ parameter ∈ parameters, isReserved parameter.1 = false)
    (closing : rest.head? = some (.symbol ')')) :
    parseTypedParameters (typedParameterTokens parameters ++ rest) = some (parameters, rest) := by
  cases parameters with
  | nil => simp [typedParameterTokens, parseTypedParameters, closing]
  | cons parameter more =>
      have notClosing : (typedParameterTokens (parameter :: more) ++ rest).head? ≠
          some (.symbol ')') := by
        cases more <;> simp [typedParameterTokens]
      rw [parseTypedParameters, if_neg notClosing]
      have := typedParameterTokens_length (parameter :: more)
      exact parseTypedParameterList_tokens _ _ rest (by simp) names
        (by simp only [List.length_append]; omega) closing

theorem parseAliasList_tokens : ∀ (aliases : List (String × String)) (fuel : Nat)
    (rest : List Token), aliases ≠ [] → aliases.length ≤ fuel →
    rest.head? = some (.symbol '}') →
    parseAliasList fuel (aliasTokens aliases ++ rest) = some (aliases, rest)
  | [], _, _, nonempty, _, _ => absurd rfl nonempty
  | [alias], fuel + 1, rest, _, _, closing => by
      cases rest with
      | nil => simp at closing
      | cons first tail =>
          simp only [List.head?_cons, Option.some.injEq] at closing
          subst closing
          simp [aliasTokens, parseAliasList]
  | alias :: next :: more, fuel + 1, rest, _, enough, closing => by
      have tailParse := parseAliasList_tokens (next :: more) fuel rest (by simp)
        (by simp only [List.length_cons] at enough ⊢; omega) closing
      simp only [aliasTokens, List.cons_append, List.nil_append]
      simp [parseAliasList, tailParse]
  | _ :: _, 0, _, _, enough, _ => absurd enough (by simp)

theorem aliasTokens_length : (aliases : List (String × String)) →
    aliases.length ≤ (aliasTokens aliases).length
  | [] => Nat.le_refl _
  | [_] => by simp [aliasTokens]
  | _ :: next :: more => by
      have := aliasTokens_length (next :: more)
      simp only [aliasTokens, List.length_append, List.length_cons] at this ⊢
      omega

theorem parseAliasImport_tokens (aliases : List (String × String)) (rest : List Token)
    (next : rest.head? ≠ some (.ident "import")) :
    parseAliasImport (aliasImportTokens aliases ++ rest) = some (aliases, rest) := by
  cases aliases with
  | nil => simp [aliasImportTokens, parseAliasImport, next]
  | cons alias more =>
      have bound : ∀ fuel, (aliasTokens (alias :: more)).length ≤ fuel →
          parseAliasList fuel (aliasTokens (alias :: more) ++ .symbol '}' :: .ident "from" ::
            .ident "std" :: .symbol '.' :: .ident "opcodes" :: .symbol ';' :: rest) =
          some (alias :: more, .symbol '}' :: .ident "from" :: .ident "std" :: .symbol '.' ::
            .ident "opcodes" :: .symbol ';' :: rest) :=
        fun fuel enough => parseAliasList_tokens (alias :: more) fuel _ (by simp)
          (Nat.le_trans (aliasTokens_length _) enough) rfl
      simp [aliasImportTokens, parseAliasImport, expectTokens]
      rw [bound _ (by omega)]
      simp [expectTokens]

/-- Every name of a free function is a non-reserved word. -/
def FunctionDecl.NamesOk (function : FunctionDecl) : Prop :=
  isReserved function.name = false ∧
    (∀ parameter ∈ function.parameters, isReserved parameter.1 = false) ∧
    Stmt.ListNamesOk function.body ∧ function.result.NamesOk

theorem parseFunction_tokens (function : FunctionDecl) (names : function.NamesOk) (fuel : Nat)
    (bodyFuel : Stmt.listSize function.body < fuel) (resultFuel : function.result.size < fuel)
    (rest : List Token) :
    parseFunction fuel (function.tokens ++ rest) = some (function, rest) := by
  obtain ⟨nameOk, parametersOk, bodyOk, resultOk⟩ := names
  have bodyParse := parseStmts_tokens (fuel := fuel)
    (rest := .ident "return" :: (function.result.tokens ++ (.symbol ';' :: .symbol '}' :: rest)))
    bodyOk bodyFuel rfl
  have resultParse := parseExpr_tokens function.result fuel
    (.symbol ';' :: .symbol '}' :: rest) resultOk resultFuel (by simp)
  have parametersParse := parseTypedParameters_tokens function.parameters
    (.symbol ')' :: .ident "returns" :: .symbol '(' :: (function.resultType.tokens ++
      (.symbol ')' :: .symbol '{' :: (Stmt.listTokens function.body ++ (.ident "return" ::
        (function.result.tokens ++ (.symbol ';' :: .symbol '}' :: rest)))))))
    parametersOk rfl
  simp only [parseFunction, FunctionDecl.tokens, List.append_assoc, List.cons_append,
    List.nil_append]
  simp [expectTokens, parseName_cons nameOk, parametersParse, LocalType.parse_tokens,
    bodyParse, resultParse]

theorem parseFunctions_tokens : ∀ (functions : List FunctionDecl) (count fuel : Nat)
    (rest : List Token),
    (∀ function ∈ functions, function.NamesOk ∧ Stmt.listSize function.body < fuel ∧
      function.result.size < fuel) →
    functions.length < count → rest.head? ≠ some (.ident "function") →
    parseFunctions count fuel (functions.flatMap FunctionDecl.tokens ++ rest) =
      some (functions, rest)
  | [], count + 1, fuel, rest, _, _, next => by
      simp [parseFunctions, next]
  | function :: more, count + 1, fuel, rest, ok, enough, next => by
      obtain ⟨names, bodyFuel, resultFuel⟩ := ok function (by simp)
      have tailParse := parseFunctions_tokens more count fuel rest
        (fun other mem => ok other (List.mem_cons_of_mem _ mem))
        (by simp only [List.length_cons] at enough; omega) next
      have functionParse := parseFunction_tokens function names fuel bodyFuel resultFuel
        (more.flatMap FunctionDecl.tokens ++ rest)
      simp only [List.flatMap_cons, List.append_assoc]
      rw [parseFunctions, if_pos (by simp [FunctionDecl.tokens])]
      simp [functionParse, tailParse]
  | _, 0, _, _, _, enough, _ => absurd enough (Nat.not_lt_zero _)

theorem Expr.size_le_tokens : (expression : Expr) → expression.size ≤ expression.tokens.length
  | .name _ | .number _ | .bool _ => by simp [Expr.size, Expr.tokens]
  | .unary _ operand => by
      have := Expr.size_le_tokens operand
      simp [Expr.size, Expr.tokens]
      omega
  | .binary _ left right => by
      have := Expr.size_le_tokens left
      have := Expr.size_le_tokens right
      simp [Expr.size, Expr.tokens]
      omega
  | .typedefRep operand => by
      have := Expr.size_le_tokens operand
      simp [Expr.size, Expr.tokens]
      omega
  | .uint256 operand => by
      have := Expr.size_le_tokens operand
      simp [Expr.size, Expr.tokens]
      omega
  | .call1 _ first => by
      have := Expr.size_le_tokens first
      simp [Expr.size, Expr.tokens]
      omega
  | .call2 _ first second => by
      have := Expr.size_le_tokens first
      have := Expr.size_le_tokens second
      simp [Expr.size, Expr.tokens]
      omega
  | .call3 _ first second third => by
      have := Expr.size_le_tokens first
      have := Expr.size_le_tokens second
      have := Expr.size_le_tokens third
      simp [Expr.size, Expr.tokens]
      omega
  | .tuple first second => by
      have := Expr.size_le_tokens first
      have := Expr.size_le_tokens second
      simp [Expr.size, Expr.tokens]
      omega
  | .inl payload => by
      have := Expr.size_le_tokens payload
      simp [Expr.size, Expr.tokens]
      omega
  | .inr payload => by
      have := Expr.size_le_tokens payload
      simp [Expr.size, Expr.tokens]
      omega

theorem Stmt.size_bounds (fuel : Nat) :
    (∀ statement : Stmt, statement.size < fuel → statement.size < statement.tokens.length) ∧
    (∀ statements : List Stmt, Stmt.listSize statements < fuel →
      Stmt.listSize statements ≤ (Stmt.listTokens statements).length) := by
  induction fuel with
  | zero =>
      exact ⟨fun _ enough => absurd enough (Nat.not_lt_zero _),
        fun _ enough => absurd enough (Nat.not_lt_zero _)⟩
  | succ fuel ih =>
      refine ⟨?_, ?_⟩
      · intro statement enough
        cases statement with
        | letDecl identifier type initializer =>
            have := Expr.size_le_tokens initializer
            simp [Stmt.size, Stmt.tokens]
            omega
        | assign identifier value =>
            have := Expr.size_le_tokens value
            simp [Stmt.size, Stmt.tokens]
            omega
        | ifElse condition thenBlock elseBlock =>
            have := Expr.size_le_tokens condition
            have := ih.2 thenBlock (by simp only [Stmt.size] at enough; omega)
            have := ih.2 elseBlock (by simp only [Stmt.size] at enough; omega)
            simp [Stmt.size, Stmt.tokens]
            omega
        | matchPair scrutinee first second body =>
            have := Expr.size_le_tokens scrutinee
            have := ih.2 body (by simp only [Stmt.size] at enough; omega)
            simp [Stmt.size, Stmt.tokens]
            omega
        | matchSum scrutinee left leftBody right rightBody =>
            have := Expr.size_le_tokens scrutinee
            have := ih.2 leftBody (by simp only [Stmt.size] at enough; omega)
            have := ih.2 rightBody (by simp only [Stmt.size] at enough; omega)
            simp [Stmt.size, Stmt.tokens]
            omega
      · intro statements enough
        cases statements with
        | nil => simp [Stmt.listSize, Stmt.listTokens]
        | cons statement tail =>
            have := ih.1 statement (by simp only [Stmt.listSize] at enough; omega)
            have := ih.2 tail (by simp only [Stmt.listSize] at enough; omega)
            simp [Stmt.listSize, Stmt.listTokens]
            omega

theorem Stmt.listSize_le_tokens (statements : List Stmt) :
    Stmt.listSize statements ≤ (Stmt.listTokens statements).length :=
  (Stmt.size_bounds (Stmt.listSize statements + 1)).2 statements (Nat.lt_succ_self _)

theorem FunctionDecl.sizes_le_tokens (function : FunctionDecl) :
    Stmt.listSize function.body < function.tokens.length ∧
      function.result.size < function.tokens.length := by
  have bodySize := Stmt.listSize_le_tokens function.body
  have resultSize := Expr.size_le_tokens function.result
  simp only [FunctionDecl.tokens, List.length_append, List.length_cons, List.length_nil]
  omega

theorem functions_sizes_le_tokens {functions : List FunctionDecl} {function : FunctionDecl}
    (mem : function ∈ functions) :
    Stmt.listSize function.body < (functions.flatMap FunctionDecl.tokens).length ∧
      function.result.size < (functions.flatMap FunctionDecl.tokens).length := by
  induction functions with
  | nil => cases mem
  | cons head rest ih =>
      simp only [List.flatMap_cons, List.length_append]
      rcases List.mem_cons.mp mem with same | mem
      · subst same
        have := function.sizes_le_tokens
        omega
      · have := ih mem
        omega

theorem functions_length_le_tokens (functions : List FunctionDecl) :
    functions.length ≤ (functions.flatMap FunctionDecl.tokens).length := by
  induction functions with
  | nil => simp
  | cons function rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have : 1 ≤ function.tokens.length := by simp [FunctionDecl.tokens]
      omega

def SourceFile.NamesOk (file : SourceFile) : Prop :=
  (∀ function ∈ file.functions, function.NamesOk) ∧
    isReserved file.contract = false ∧ isReserved file.method.name = false ∧
    (∀ parameter ∈ file.method.parameters, isReserved parameter = false) ∧
    Stmt.ListNamesOk file.method.body ∧ file.method.result.NamesOk

theorem parseFileWith_tokens (file : SourceFile) (names : file.NamesOk) (fuel : Nat)
    (functionsFuel : ∀ function ∈ file.functions,
      Stmt.listSize function.body < fuel ∧ function.result.size < fuel)
    (bodyFuel : Stmt.listSize file.method.body < fuel)
    (resultFuel : file.method.result.size < fuel) :
    parseFileWith fuel file.tokens = some file := by
  obtain ⟨functionsOk, contractOk, methodOk, parametersOk, bodyOk, resultOk⟩ := names
  have bodyParse := parseStmts_tokens (fuel := fuel)
    (rest := .ident "return" :: (file.method.result.tokens ++
      [.symbol ';', .symbol '}', .symbol '}'])) bodyOk bodyFuel rfl
  have resultParse := parseExpr_tokens file.method.result fuel
    [.symbol ';', .symbol '}', .symbol '}'] resultOk resultFuel (by simp)
  have parametersParse := parseParameters_tokens file.method.parameters
    (signatureTokens ++ (Stmt.listTokens file.method.body ++ (.ident "return" ::
      (file.method.result.tokens ++ [.symbol ';', .symbol '}', .symbol '}'])))) parametersOk rfl
  have functionsLength := functions_length_le_tokens file.functions
  have functionsParse := parseFunctions_tokens file.functions (file.tokens.length + 1) fuel
    (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
      .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
        (signatureTokens ++ (Stmt.listTokens file.method.body ++ (.ident "return" ::
          (file.method.result.tokens ++ [.symbol ';', .symbol '}', .symbol '}']))))))
    (fun function mem => ⟨functionsOk function mem, functionsFuel function mem⟩)
    (by simp only [SourceFile.tokens, List.length_append] at functionsLength ⊢; omega)
    (by simp)
  have aliasesParse := parseAliasImport_tokens file.opcodeAliases
    (file.functions.flatMap FunctionDecl.tokens ++
      (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
        .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
          (signatureTokens ++ (Stmt.listTokens file.method.body ++ (.ident "return" ::
            (file.method.result.tokens ++ [.symbol ';', .symbol '}', .symbol '}'])))))))
    (by
      cases functions : file.functions with
      | nil => simp
      | cons function rest => simp [FunctionDecl.tokens])
  unfold parseFileWith
  conv => lhs; arg 1; rw [SourceFile.tokens]
  simp only [List.append_assoc, List.cons_append, List.nil_append, expectTokens_append,
    Option.bind_eq_bind, Option.bind_some]
  rw [aliasesParse]
  simp only [Option.bind_some]
  rw [functionsParse]
  simp [expectTokens, parseName_cons contractOk, parseName_cons methodOk, parametersParse,
    expectTokens_append, bodyParse, resultParse]

/-- **Parser round trip.** Parsing the tokens of a file with non-reserved
names returns that file. -/
theorem parseFile_tokens (file : SourceFile) (names : file.NamesOk) :
    parseFile file.tokens = some file := by
  have bodySize := Stmt.listSize_le_tokens file.method.body
  have resultSize := Expr.size_le_tokens file.method.result
  apply parseFileWith_tokens file names
  · intro function mem
    have := functions_sizes_le_tokens mem
    simp only [SourceFile.tokens, List.length_append]
    omega
  · simp only [SourceFile.tokens, List.length_append] at bodySize ⊢
    omega
  · simp only [SourceFile.tokens, List.length_append] at resultSize ⊢
    omega

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.Print
/-! Concrete text of the source fragment, in the exact layout used by the
source renderers and their wrappers: `pragma solcore;` on the first line,
four-space indentation steps, one statement, case header or brace per line, a
blank line after the imports and after every free function, and a trailing
newline. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

def indentLine (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

def Expr.print : Expr → String
  | .name identifier => identifier
  | .number value => toString value
  | .bool value => if value then "true" else "false"
  | .unary op operand => "(" ++ op.spelling ++ operand.print ++ ")"
  | .binary op left right =>
      "(" ++ left.print ++ " " ++ op.spelling ++ " " ++ right.print ++ ")"
  | .typedefRep operand => "Typedef.rep(" ++ operand.print ++ ")"
  | .uint256 operand => "uint256(" ++ operand.print ++ ")"
  | .call1 callee first => callee ++ "(" ++ first.print ++ ")"
  | .call2 callee first second => callee ++ "(" ++ first.print ++ ", " ++ second.print ++ ")"
  | .call3 callee first second third =>
      callee ++ "(" ++ first.print ++ ", " ++ second.print ++ ", " ++ third.print ++ ")"
  | .tuple first second => "(" ++ first.print ++ ", " ++ second.print ++ ")"
  | .inl payload => "inl(" ++ payload.print ++ ")"
  | .inr payload => "inr(" ++ payload.print ++ ")"

mutual

/-- The lines of one statement at the given indentation. Branch blocks and
case headers are indented by four further spaces, case bodies by eight. -/
def Stmt.lines (indent : Nat) : Stmt → List String
  | .letDecl identifier type initializer =>
      [indentLine indent
        ("let " ++ identifier ++ ": " ++ type.spelling ++ " = " ++ initializer.print ++ ";")]
  | .assign identifier value =>
      [indentLine indent (identifier ++ " = " ++ value.print ++ ";")]
  | .ifElse condition thenBlock elseBlock =>
      [indentLine indent ("if (" ++ condition.print ++ ") {")] ++
        Stmt.listLines (indent + 4) thenBlock ++ [indentLine indent "} else {"] ++
        Stmt.listLines (indent + 4) elseBlock ++ [indentLine indent "}"]
  | .matchPair scrutinee first second body =>
      [indentLine indent ("match (" ++ scrutinee.print ++ ") {"),
        indentLine (indent + 4) ("case (" ++ first ++ ", " ++ second ++ ") {")] ++
        Stmt.listLines (indent + 8) body ++
        [indentLine (indent + 4) "}", indentLine indent "}"]
  | .matchSum scrutinee left leftBody right rightBody =>
      [indentLine indent ("match (" ++ scrutinee.print ++ ") {"),
        indentLine (indent + 4) ("case inl(" ++ left ++ ") {")] ++
        Stmt.listLines (indent + 8) leftBody ++
        [indentLine (indent + 4) "}", indentLine (indent + 4) ("case inr(" ++ right ++ ") {")] ++
        Stmt.listLines (indent + 8) rightBody ++
        [indentLine (indent + 4) "}", indentLine indent "}"]

def Stmt.listLines (indent : Nat) : List Stmt → List String
  | [] => []
  | statement :: rest => statement.lines indent ++ Stmt.listLines indent rest

end

theorem Stmt.listLines_append (indent : Nat) (first second : List Stmt) :
    Stmt.listLines indent (first ++ second) =
      Stmt.listLines indent first ++ Stmt.listLines indent second := by
  induction first with
  | nil => simp [Stmt.listLines]
  | cons statement rest ih =>
      simp [Stmt.listLines, ih, List.append_assoc]

/-- The parameter list between a free function's parentheses. -/
def FunctionDecl.parameterText (parameters : List (String × LocalType)) : String :=
  String.intercalate ", " (parameters.map fun parameter =>
    parameter.1 ++ ": " ++ parameter.2.spelling)

/-- A free function, followed by one blank line. -/
def FunctionDecl.lines (function : FunctionDecl) : List String :=
  ["function " ++ function.name ++ "(" ++ FunctionDecl.parameterText function.parameters ++
      ") returns (" ++ function.resultType.spelling ++ ") {"] ++
    Stmt.listLines 4 function.body ++
    ["    return " ++ function.result.print ++ ";", "}", ""]

/-- The parameter list between the method's parentheses. -/
def Method.parameterText (parameters : List String) : String :=
  String.intercalate ", " (parameters.map (· ++ ": uint256"))

/-- `import { opcode as alias, ... } from std.opcodes;` -/
def aliasImportLine (aliases : List (String × String)) : String :=
  "import { " ++ String.intercalate ", " (aliases.map fun alias =>
    alias.1 ++ " as " ++ alias.2) ++ " } from std.opcodes;"

/-- No line without aliases. -/
def aliasImportLines : List (String × String) → List String
  | [] => []
  | alias :: rest => [aliasImportLine (alias :: rest)]

def SourceFile.lines (file : SourceFile) : List String :=
  ["pragma solcore;", "import * from std;", "import * from std.dispatch;"] ++
  aliasImportLines file.opcodeAliases ++ [""] ++
  file.functions.flatMap FunctionDecl.lines ++
  ["contract " ++ file.contract ++ " {",
    "    function " ++ file.method.name ++ "(" ++ Method.parameterText file.method.parameters ++
      ") public returns (uint256) {"] ++
  Stmt.listLines 8 file.method.body ++
  ["        return " ++ file.method.result.print ++ ";", "    }", "}"]

def SourceFile.print (file : SourceFile) : String :=
  String.intercalate "\n" file.lines ++ "\n"

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.Text
/-! Meaning of a source text. `parseSource` lexes and parses a complete text
of the fragment; `sourceCall` then calls a method under the independent source
semantics. The printed text of every file with valid, non-reserved names
parses back to that file. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

def parseSource (source : String) : Option SourceFile :=
  (lex source.toList).bind parseFile

/-- The returned ABI word of calling `method` on the contract written in
`source`, when the text belongs to the fragment and the call has a meaning. -/
def sourceCall (source : String) (method : String) (arguments : List Nat) : Option Nat :=
  (parseSource source).bind fun file => file.call method arguments

/-! ### Separation of concatenated pieces -/

def Piece.SafeRight (piece : Piece) : Prop :=
  piece.wordLike = false ∧ piece ≠ .token (.symbol '=')

def Piece.SafeLeft (piece : Piece) : Prop :=
  piece.wordLike = false ∧ piece.startsWithEqual = false

theorem Separated.cons_safe {piece : Piece} {rest : List Piece} (valid : piece.Valid)
    (safe : piece.SafeRight) (separated : Separated rest) : Separated (piece :: rest) := by
  cases rest with
  | nil => exact valid
  | cons next tail =>
      refine ⟨valid, ⟨fun both => ?_, fun both => safe.2 both.1⟩, separated⟩
      rw [safe.1] at both
      cases both.1

theorem Separated.cons_before {piece : Piece} {rest : List Piece} (valid : piece.Valid)
    (separated : Separated rest) (safe : ∀ next ∈ rest.head?, next.SafeLeft) :
    Separated (piece :: rest) := by
  cases rest with
  | nil => exact valid
  | cons next tail =>
      have nextSafe := safe next rfl
      refine ⟨valid, ⟨fun both => ?_, fun both => ?_⟩, separated⟩
      · rw [nextSafe.1] at both
        cases both.2
      · rw [nextSafe.2] at both
        cases both.2

theorem Separated.append_before {first second : List Piece} (separatedFirst : Separated first)
    (separatedSecond : Separated second) (safe : ∀ next ∈ second.head?, next.SafeLeft) :
    Separated (first ++ second) := by
  induction first with
  | nil => exact separatedSecond
  | cons piece rest ih =>
      cases rest with
      | nil => exact Separated.cons_before separatedFirst separatedSecond safe
      | cons next tail => exact ⟨separatedFirst.1, separatedFirst.2.1, ih separatedFirst.2.2⟩

def space : Piece := .blank ' '
def word (text : String) : Piece := .token (.ident text)
def sym (char : Char) : Piece := .token (.symbol char)
def blanks (count : Nat) : List Piece := List.replicate count space

theorem space_valid : space.Valid := rfl
theorem space_safeRight : space.SafeRight := ⟨rfl, by simp [space]⟩
theorem space_safeLeft : space.SafeLeft := ⟨rfl, rfl⟩

theorem sym_valid {char : Char} (symbol : isSymbolChar char = true) : (sym char).Valid :=
  Or.inl symbol

theorem sym_safeRight {char : Char} (symbol : isSymbolChar char = true) :
    (sym char).SafeRight :=
  ⟨rfl, fun same => (symbol_classes symbol).2.2.2.2 (by cases same; rfl)⟩

theorem sym_safeLeft {char : Char} (symbol : isSymbolChar char = true) : (sym char).SafeLeft := by
  refine ⟨rfl, ?_⟩
  simp only [sym, Piece.startsWithEqual, beq_eq_false_iff_ne, ne_eq]
  exact (symbol_classes symbol).2.2.2.2

theorem word_valid {text : String} (valid : ValidIdentifier text) : (word text).Valid := valid

/-- Symbol pieces are separated from anything on both sides. -/
theorem Separated.cons_sym {char : Char} {rest : List Piece} (symbol : isSymbolChar char = true)
    (separated : Separated rest) : Separated (sym char :: rest) :=
  Separated.cons_safe (sym_valid symbol) (sym_safeRight symbol) separated

theorem Separated.cons_space {rest : List Piece} (separated : Separated rest) :
    Separated (space :: rest) :=
  Separated.cons_safe space_valid space_safeRight separated

theorem Separated.blanks_append {rest : List Piece} (count : Nat) (separated : Separated rest) :
    Separated (blanks count ++ rest) := by
  induction count with
  | zero => exact separated
  | succ count ih => exact Separated.cons_space ih

theorem render_blanks (count : Nat) : render (blanks count) = List.replicate count ' ' := by
  induction count with
  | zero => rfl
  | succ count ih => simp [blanks, List.replicate_succ, render, Piece.chars, space] at ih ⊢; exact ih

theorem tokensOf_blanks (count : Nat) : tokensOf (blanks count) = [] := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [blanks, List.replicate_succ, tokensOf, space] using ih

/-! ### Expressions -/

def Expr.pieces : Expr → List Piece
  | .name identifier => [word identifier]
  | .number value => [.token (.number value)]
  | .bool value => [word (if value then "true" else "false")]
  | .unary op operand => [sym '(', .token op.token] ++ operand.pieces ++ [sym ')']
  | .binary op left right =>
      [sym '('] ++ left.pieces ++ [space, .token op.token, space] ++ right.pieces ++ [sym ')']
  | .typedefRep operand =>
      [word "Typedef", sym '.', word "rep", sym '('] ++ operand.pieces ++ [sym ')']
  | .uint256 operand => [word "uint256", sym '('] ++ operand.pieces ++ [sym ')']
  | .call1 callee first => [word callee, sym '('] ++ first.pieces ++ [sym ')']
  | .call2 callee first second =>
      [word callee, sym '('] ++ first.pieces ++ [sym ',', space] ++ second.pieces ++ [sym ')']
  | .call3 callee first second third =>
      [word callee, sym '('] ++ first.pieces ++ [sym ',', space] ++ second.pieces ++
        [sym ',', space] ++ third.pieces ++ [sym ')']
  | .tuple first second =>
      [sym '('] ++ first.pieces ++ [sym ',', space] ++ second.pieces ++ [sym ')']
  | .inl payload => [word "inl", sym '('] ++ payload.pieces ++ [sym ')']
  | .inr payload => [word "inr", sym '('] ++ payload.pieces ++ [sym ')']

theorem UnaryOp.spelling_toList (op : UnaryOp) : op.spelling.toList = op.token.chars := by
  cases op <;> rfl

theorem BinaryOp.spelling_toList (op : BinaryOp) : op.spelling.toList = op.token.chars := by
  cases op <;> rfl

theorem Expr.print_toList : (expression : Expr) → expression.print.toList = render expression.pieces
  | .name identifier => by simp [Expr.print, Expr.pieces, render, Piece.chars, Token.chars, word]
  | .number value => by
      simp [Expr.print, Expr.pieces, render, Piece.chars, Token.chars]
  | .bool value => by
      cases value <;> simp [Expr.print, Expr.pieces, render, Piece.chars, Token.chars, word]
  | .unary op operand => by
      simp [Expr.print, Expr.pieces, render_append, render, Piece.chars, Token.chars, sym,
        UnaryOp.spelling_toList, Expr.print_toList operand]
  | .binary op left right => by
      simp [Expr.print, Expr.pieces, render_append, render, Piece.chars, Token.chars, sym, space,
        BinaryOp.spelling_toList, Expr.print_toList left, Expr.print_toList right]
  | .typedefRep operand => by
      simp [Expr.print, Expr.pieces, render_append, render, Piece.chars, Token.chars, sym, word,
        Expr.print_toList operand]
  | .uint256 operand => by
      simp [Expr.print, Expr.pieces, render_append, render, Piece.chars, Token.chars, sym, word,
        Expr.print_toList operand]
  | .call1 callee first => by
      simp [Expr.print, Expr.pieces, render_append, render, Piece.chars, Token.chars, sym, word,
        Expr.print_toList first]
  | .call2 callee first second => by
      simp [Expr.print, Expr.pieces, render_append, render, Piece.chars, Token.chars, sym, word,
        space, Expr.print_toList first, Expr.print_toList second]
  | .call3 callee first second third => by
      simp [Expr.print, Expr.pieces, render_append, render, Piece.chars, Token.chars, sym, word,
        space, Expr.print_toList first, Expr.print_toList second, Expr.print_toList third]
  | .tuple first second => by
      simp [Expr.print, Expr.pieces, render_append, render, Piece.chars, Token.chars, sym,
        space, Expr.print_toList first, Expr.print_toList second]
  | .inl payload => by
      simp [Expr.print, Expr.pieces, render_append, render, Piece.chars, Token.chars, sym, word,
        Expr.print_toList payload]
  | .inr payload => by
      simp [Expr.print, Expr.pieces, render_append, render, Piece.chars, Token.chars, sym, word,
        Expr.print_toList payload]

theorem Expr.tokensOf_pieces : (expression : Expr) → tokensOf expression.pieces = expression.tokens
  | .name identifier => rfl
  | .number value => rfl
  | .bool value => rfl
  | .unary op operand => by
      simp [Expr.pieces, Expr.tokens, tokensOf_append, tokensOf, sym,
        Expr.tokensOf_pieces operand]
  | .binary op left right => by
      simp [Expr.pieces, Expr.tokens, tokensOf_append, tokensOf, sym, space,
        Expr.tokensOf_pieces left, Expr.tokensOf_pieces right]
  | .typedefRep operand => by
      simp [Expr.pieces, Expr.tokens, tokensOf_append, tokensOf, sym, word,
        Expr.tokensOf_pieces operand]
  | .uint256 operand => by
      simp [Expr.pieces, Expr.tokens, tokensOf_append, tokensOf, sym, word,
        Expr.tokensOf_pieces operand]
  | .call1 callee first => by
      simp [Expr.pieces, Expr.tokens, tokensOf_append, tokensOf, sym, word,
        Expr.tokensOf_pieces first]
  | .call2 callee first second => by
      simp [Expr.pieces, Expr.tokens, tokensOf_append, tokensOf, sym, word, space,
        Expr.tokensOf_pieces first, Expr.tokensOf_pieces second]
  | .call3 callee first second third => by
      simp [Expr.pieces, Expr.tokens, tokensOf_append, tokensOf, sym, word, space,
        Expr.tokensOf_pieces first, Expr.tokensOf_pieces second, Expr.tokensOf_pieces third]
  | .tuple first second => by
      simp [Expr.pieces, Expr.tokens, tokensOf_append, tokensOf, sym, space,
        Expr.tokensOf_pieces first, Expr.tokensOf_pieces second]
  | .inl payload => by
      simp [Expr.pieces, Expr.tokens, tokensOf_append, tokensOf, sym, word,
        Expr.tokensOf_pieces payload]
  | .inr payload => by
      simp [Expr.pieces, Expr.tokens, tokensOf_append, tokensOf, sym, word,
        Expr.tokensOf_pieces payload]

def Expr.IdentifiersValid (expression : Expr) : Prop :=
  ∀ name ∈ expression.identifiers, ValidIdentifier name

theorem UnaryOp.token_valid (op : UnaryOp) : (Piece.token op.token).Valid ∧
    (Piece.token op.token).SafeRight := by
  cases op
  · exact ⟨sym_valid (by decide), sym_safeRight (by decide)⟩
  · exact ⟨sym_valid (by decide), sym_safeRight (by decide)⟩

theorem BinaryOp.token_valid (op : BinaryOp) : (Piece.token op.token).Valid ∧
    (Piece.token op.token).SafeRight := by
  cases op
  case eq => exact ⟨trivial, rfl, by simp [BinaryOp.token]⟩
  all_goals exact ⟨sym_valid (by decide), sym_safeRight (by decide)⟩

/-- An expression followed by a piece that is safe on its left is separated. -/
theorem Expr.separated_append : (expression : Expr) → expression.IdentifiersValid →
    ∀ (rest : List Piece), Separated rest → (∀ next ∈ rest.head?, next.SafeLeft) →
    Separated (expression.pieces ++ rest)
  | .name identifier, valid, rest, separated, safe =>
      Separated.cons_before (word_valid (valid identifier (by simp [Expr.identifiers])))
        separated safe
  | .number value, _, rest, separated, safe =>
      Separated.cons_before (piece := .token (.number value)) trivial separated safe
  | .bool value, _, rest, separated, safe => by
      have valid : ValidIdentifier (if value then "true" else "false") := by
        cases value
        · exact ValidIdentifier.of_check (by decide)
        · exact ValidIdentifier.of_check (by decide)
      exact Separated.cons_before (word_valid valid) separated safe
  | .unary op operand, valid, rest, separated, safe => by
      have inner := Expr.separated_append operand (fun name mem => valid name mem)
        (sym ')' :: rest) (Separated.cons_sym (by decide) separated)
        (fun next same => by cases same; exact sym_safeLeft (by decide))
      simp only [Expr.pieces, List.append_assoc, List.cons_append, List.nil_append]
      exact Separated.cons_sym (by decide)
        (Separated.cons_safe (UnaryOp.token_valid op).1 (UnaryOp.token_valid op).2 inner)
  | .binary op left right, valid, rest, separated, safe => by
      have rightPart := Expr.separated_append right
        (fun name mem => valid name (by simp [Expr.identifiers, mem]))
        (sym ')' :: rest) (Separated.cons_sym (by decide) separated)
        (fun next same => by cases same; exact sym_safeLeft (by decide))
      have middle : Separated (space :: .token op.token :: space :: (right.pieces ++
          sym ')' :: rest)) :=
        Separated.cons_space (Separated.cons_safe (BinaryOp.token_valid op).1
          (BinaryOp.token_valid op).2 (Separated.cons_space rightPart))
      have leftPart := Expr.separated_append left
        (fun name mem => valid name (by simp [Expr.identifiers, mem])) _ middle
        (fun next same => by cases same; exact space_safeLeft)
      simp only [Expr.pieces, List.append_assoc, List.cons_append, List.nil_append]
      exact Separated.cons_sym (by decide) leftPart
  | .typedefRep operand, valid, rest, separated, safe => by
      have inner := Expr.separated_append operand (fun name mem => valid name mem)
        (sym ')' :: rest) (Separated.cons_sym (by decide) separated)
        (fun next same => by cases same; exact sym_safeLeft (by decide))
      simp only [Expr.pieces, List.append_assoc, List.cons_append, List.nil_append]
      refine Separated.cons_before (word_valid (ValidIdentifier.of_check (by decide)))
        (Separated.cons_sym (by decide) (Separated.cons_before
          (word_valid (ValidIdentifier.of_check (by decide)))
          (Separated.cons_sym (by decide) inner) ?_)) ?_
      · intro next same
        cases same
        exact sym_safeLeft (by decide)
      · intro next same
        cases same
        exact sym_safeLeft (by decide)
  | .uint256 operand, valid, rest, separated, safe => by
      have inner := Expr.separated_append operand (fun name mem => valid name mem)
        (sym ')' :: rest) (Separated.cons_sym (by decide) separated)
        (fun next same => by cases same; exact sym_safeLeft (by decide))
      simp only [Expr.pieces, List.append_assoc, List.cons_append, List.nil_append]
      refine Separated.cons_before (word_valid (ValidIdentifier.of_check (by decide)))
        (Separated.cons_sym (by decide) inner) ?_
      intro next same
      cases same
      exact sym_safeLeft (by decide)
  | .call1 callee first, valid, rest, separated, safe => by
      have inner := Expr.separated_append first
        (fun name mem => valid name (by simp [Expr.identifiers, mem]))
        (sym ')' :: rest) (Separated.cons_sym (by decide) separated)
        (fun next same => by cases same; exact sym_safeLeft (by decide))
      simp only [Expr.pieces, List.append_assoc, List.cons_append, List.nil_append]
      refine Separated.cons_before (word_valid (valid callee (by simp [Expr.identifiers])))
        (Separated.cons_sym (by decide) inner) ?_
      intro next same
      cases same
      exact sym_safeLeft (by decide)
  | .call2 callee first second, valid, rest, separated, safe => by
      have secondPart := Expr.separated_append second
        (fun name mem => valid name (by simp [Expr.identifiers, mem]))
        (sym ')' :: rest) (Separated.cons_sym (by decide) separated)
        (fun next same => by cases same; exact sym_safeLeft (by decide))
      have firstPart := Expr.separated_append first
        (fun name mem => valid name (by simp [Expr.identifiers, mem]))
        (sym ',' :: space :: (second.pieces ++ sym ')' :: rest))
        (Separated.cons_sym (by decide) (Separated.cons_space secondPart))
        (fun next same => by cases same; exact sym_safeLeft (by decide))
      simp only [Expr.pieces, List.append_assoc, List.cons_append, List.nil_append]
      refine Separated.cons_before (word_valid (valid callee (by simp [Expr.identifiers])))
        (Separated.cons_sym (by decide) firstPart) ?_
      intro next same
      cases same
      exact sym_safeLeft (by decide)
  | .call3 callee first second third, valid, rest, separated, safe => by
      have thirdPart := Expr.separated_append third
        (fun name mem => valid name (by simp [Expr.identifiers, mem]))
        (sym ')' :: rest) (Separated.cons_sym (by decide) separated)
        (fun next same => by cases same; exact sym_safeLeft (by decide))
      have secondPart := Expr.separated_append second
        (fun name mem => valid name (by simp [Expr.identifiers, mem]))
        (sym ',' :: space :: (third.pieces ++ sym ')' :: rest))
        (Separated.cons_sym (by decide) (Separated.cons_space thirdPart))
        (fun next same => by cases same; exact sym_safeLeft (by decide))
      have firstPart := Expr.separated_append first
        (fun name mem => valid name (by simp [Expr.identifiers, mem]))
        (sym ',' :: space :: (second.pieces ++ sym ',' :: space :: (third.pieces ++
          sym ')' :: rest)))
        (Separated.cons_sym (by decide) (Separated.cons_space secondPart))
        (fun next same => by cases same; exact sym_safeLeft (by decide))
      simp only [Expr.pieces, List.append_assoc, List.cons_append, List.nil_append]
      refine Separated.cons_before (word_valid (valid callee (by simp [Expr.identifiers])))
        (Separated.cons_sym (by decide) firstPart) ?_
      intro next same
      cases same
      exact sym_safeLeft (by decide)
  | .tuple first second, valid, rest, separated, safe => by
      have secondPart := Expr.separated_append second
        (fun name mem => valid name (by simp [Expr.identifiers, mem]))
        (sym ')' :: rest) (Separated.cons_sym (by decide) separated)
        (fun next same => by cases same; exact sym_safeLeft (by decide))
      have firstPart := Expr.separated_append first
        (fun name mem => valid name (by simp [Expr.identifiers, mem]))
        (sym ',' :: space :: (second.pieces ++ sym ')' :: rest))
        (Separated.cons_sym (by decide) (Separated.cons_space secondPart))
        (fun next same => by cases same; exact sym_safeLeft (by decide))
      simp only [Expr.pieces, List.append_assoc, List.cons_append, List.nil_append]
      exact Separated.cons_sym (by decide) firstPart
  | .inl payload, valid, rest, separated, safe => by
      have inner := Expr.separated_append payload (fun name mem => valid name mem)
        (sym ')' :: rest) (Separated.cons_sym (by decide) separated)
        (fun next same => by cases same; exact sym_safeLeft (by decide))
      simp only [Expr.pieces, List.append_assoc, List.cons_append, List.nil_append]
      refine Separated.cons_before (word_valid (ValidIdentifier.of_check (by decide)))
        (Separated.cons_sym (by decide) inner) ?_
      intro next same
      cases same
      exact sym_safeLeft (by decide)
  | .inr payload, valid, rest, separated, safe => by
      have inner := Expr.separated_append payload (fun name mem => valid name mem)
        (sym ')' :: rest) (Separated.cons_sym (by decide) separated)
        (fun next same => by cases same; exact sym_safeLeft (by decide))
      simp only [Expr.pieces, List.append_assoc, List.cons_append, List.nil_append]
      refine Separated.cons_before (word_valid (ValidIdentifier.of_check (by decide)))
        (Separated.cons_sym (by decide) inner) ?_
      intro next same
      cases same
      exact sym_safeLeft (by decide)

theorem Separated.cons_equal {rest : List Piece} (separated : Separated rest)
    (safe : ∀ next ∈ rest.head?, next.startsWithEqual = false) :
    Separated (sym '=' :: rest) := by
  cases rest with
  | nil => exact Or.inr rfl
  | cons next tail =>
      refine ⟨Or.inr rfl, ⟨fun both => ?_, fun both => ?_⟩, separated⟩
      · cases both.1
      · rw [safe next rfl] at both
        cases both.2

theorem Separated.cons_word {text : String} {rest : List Piece} (valid : ValidIdentifier text)
    (separated : Separated rest) (safe : ∀ next ∈ rest.head?, next.SafeLeft) :
    Separated (word text :: rest) :=
  Separated.cons_before (word_valid valid) separated safe

theorem head_space {rest : List Piece} : ∀ next ∈ (space :: rest).head?, next.SafeLeft := by
  intro next same
  cases same
  exact space_safeLeft

theorem head_sym {char : Char} {rest : List Piece} (symbol : isSymbolChar char = true) :
    ∀ next ∈ (sym char :: rest).head?, next.SafeLeft := by
  intro next same
  cases same
  exact sym_safeLeft symbol

theorem keyword_valid {text : String} (check : validIdentifier text = true) :
    ValidIdentifier text :=
  ValidIdentifier.of_check check

/-- The printed pieces of a type annotation. -/
def LocalType.pieces : LocalType → List Piece
  | .word => [ScalarMeaning.word "word"]
  | .bool => [ScalarMeaning.word "bool"]
  | .wordPair =>
      [sym '(', ScalarMeaning.word "word", sym ',', space, ScalarMeaning.word "word", sym ')']
  | .wordSum =>
      [ScalarMeaning.word "sum", sym '<', ScalarMeaning.word "word", sym ',', space,
        ScalarMeaning.word "word", sym '>']

theorem LocalType.spelling_toList (type : LocalType) :
    type.spelling.toList = render type.pieces := by
  cases type <;> simp [LocalType.spelling, LocalType.pieces, render, Piece.chars, Token.chars,
    ScalarMeaning.word, sym, space]

theorem LocalType.tokensOf_pieces (type : LocalType) : tokensOf type.pieces = type.tokens := by
  cases type <;> rfl

/-- A type annotation followed by a piece that is safe on its left is
separated. -/
theorem LocalType.separated_append (type : LocalType) (rest : List Piece)
    (separated : Separated rest) (safe : ∀ next ∈ rest.head?, next.SafeLeft) :
    Separated (type.pieces ++ rest) := by
  cases type
  · exact Separated.cons_word (keyword_valid (by decide)) separated safe
  · exact Separated.cons_word (keyword_valid (by decide)) separated safe
  · exact Separated.cons_sym (by decide) (Separated.cons_word (keyword_valid (by decide))
      (Separated.cons_sym (by decide) (Separated.cons_space (Separated.cons_word
        (keyword_valid (by decide)) (Separated.cons_sym (by decide) separated)
        (head_sym (by decide))))) (head_sym (by decide)))
  · exact Separated.cons_word (keyword_valid (by decide)) (Separated.cons_sym (by decide)
      (Separated.cons_word (keyword_valid (by decide)) (Separated.cons_sym (by decide)
        (Separated.cons_space (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_sym (by decide) separated) (head_sym (by decide)))))
        (head_sym (by decide)))) (head_sym (by decide))

/-! ### Statements -/

mutual

def Stmt.linePieces (indent : Nat) : Stmt → List (List Piece)
  | .letDecl identifier type initializer =>
      [blanks indent ++ [word "let", space, word identifier, sym ':', space] ++ type.pieces ++
        [space, sym '=', space] ++ initializer.pieces ++ [sym ';']]
  | .assign identifier value =>
      [blanks indent ++ [word identifier, space, sym '=', space] ++ value.pieces ++ [sym ';']]
  | .ifElse condition thenBlock elseBlock =>
      [blanks indent ++ [word "if", space, sym '('] ++ condition.pieces ++
          [sym ')', space, sym '{']] ++
        Stmt.listLinePieces (indent + 4) thenBlock ++
        [blanks indent ++ [sym '}', space, word "else", space, sym '{']] ++
        Stmt.listLinePieces (indent + 4) elseBlock ++ [blanks indent ++ [sym '}']]
  | .matchPair scrutinee first second body =>
      [blanks indent ++ [word "match", space, sym '('] ++ scrutinee.pieces ++
          [sym ')', space, sym '{'],
        blanks (indent + 4) ++ [word "case", space, sym '(', word first, sym ',', space,
          word second, sym ')', space, sym '{']] ++
        Stmt.listLinePieces (indent + 8) body ++
        [blanks (indent + 4) ++ [sym '}'], blanks indent ++ [sym '}']]
  | .matchSum scrutinee left leftBody right rightBody =>
      [blanks indent ++ [word "match", space, sym '('] ++ scrutinee.pieces ++
          [sym ')', space, sym '{'],
        blanks (indent + 4) ++ [word "case", space, word "inl", sym '(', word left, sym ')',
          space, sym '{']] ++
        Stmt.listLinePieces (indent + 8) leftBody ++
        [blanks (indent + 4) ++ [sym '}'],
          blanks (indent + 4) ++ [word "case", space, word "inr", sym '(', word right, sym ')',
            space, sym '{']] ++
        Stmt.listLinePieces (indent + 8) rightBody ++
        [blanks (indent + 4) ++ [sym '}'], blanks indent ++ [sym '}']]

def Stmt.listLinePieces (indent : Nat) : List Stmt → List (List Piece)
  | [] => []
  | statement :: rest => statement.linePieces indent ++ Stmt.listLinePieces indent rest

end

theorem indentLine_toList (indent : Nat) (text : String) :
    (indentLine indent text).toList = List.replicate indent ' ' ++ text.toList := by
  simp [indentLine]

mutual

theorem Stmt.lines_toList (indent : Nat) : (statement : Stmt) →
    (statement.lines indent).map String.toList = (statement.linePieces indent).map render
  | .letDecl identifier type initializer => by
      simp [Stmt.lines, Stmt.linePieces, indentLine_toList, render_append, render_blanks, render,
        Piece.chars, Token.chars, word, sym, space, Expr.print_toList, LocalType.spelling_toList]
  | .assign identifier value => by
      simp [Stmt.lines, Stmt.linePieces, indentLine_toList, render_append, render_blanks, render,
        Piece.chars, Token.chars, word, sym, space, Expr.print_toList]
  | .ifElse condition thenBlock elseBlock => by
      simp [Stmt.lines, Stmt.linePieces, indentLine_toList, render_append, render_blanks, render,
        Piece.chars, Token.chars, word, sym, space, Expr.print_toList,
        Stmt.listLines_toList (indent + 4) thenBlock, Stmt.listLines_toList (indent + 4) elseBlock]
  | .matchPair scrutinee first second body => by
      simp [Stmt.lines, Stmt.linePieces, indentLine_toList, render_append, render_blanks, render,
        Piece.chars, Token.chars, word, sym, space, Expr.print_toList,
        Stmt.listLines_toList (indent + 8) body]
  | .matchSum scrutinee left leftBody right rightBody => by
      simp [Stmt.lines, Stmt.linePieces, indentLine_toList, render_append, render_blanks, render,
        Piece.chars, Token.chars, word, sym, space, Expr.print_toList,
        Stmt.listLines_toList (indent + 8) leftBody, Stmt.listLines_toList (indent + 8) rightBody]

theorem Stmt.listLines_toList (indent : Nat) : (statements : List Stmt) →
    (Stmt.listLines indent statements).map String.toList =
      (Stmt.listLinePieces indent statements).map render
  | [] => rfl
  | statement :: rest => by
      simp [Stmt.listLines, Stmt.listLinePieces, Stmt.lines_toList indent statement,
        Stmt.listLines_toList indent rest]

end

mutual

theorem Stmt.linePieces_tokens (indent : Nat) : (statement : Stmt) →
    ((statement.linePieces indent).map tokensOf).flatten = statement.tokens
  | .letDecl identifier type initializer => by
      simp [Stmt.linePieces, Stmt.tokens, tokensOf_append, tokensOf_blanks, tokensOf, word, sym,
        space, Expr.tokensOf_pieces, LocalType.tokensOf_pieces]
  | .assign identifier value => by
      simp [Stmt.linePieces, Stmt.tokens, tokensOf_append, tokensOf_blanks, tokensOf, word, sym,
        space, Expr.tokensOf_pieces]
  | .ifElse condition thenBlock elseBlock => by
      simp [Stmt.linePieces, Stmt.tokens, tokensOf_append, tokensOf_blanks, tokensOf, word, sym,
        space, Expr.tokensOf_pieces, Stmt.listLinePieces_tokens (indent + 4) thenBlock,
        Stmt.listLinePieces_tokens (indent + 4) elseBlock]
  | .matchPair scrutinee first second body => by
      simp [Stmt.linePieces, Stmt.tokens, tokensOf_append, tokensOf_blanks, tokensOf, word, sym,
        space, Expr.tokensOf_pieces, Stmt.listLinePieces_tokens (indent + 8) body]
  | .matchSum scrutinee left leftBody right rightBody => by
      simp [Stmt.linePieces, Stmt.tokens, tokensOf_append, tokensOf_blanks, tokensOf, word, sym,
        space, Expr.tokensOf_pieces, Stmt.listLinePieces_tokens (indent + 8) leftBody,
        Stmt.listLinePieces_tokens (indent + 8) rightBody]

theorem Stmt.listLinePieces_tokens (indent : Nat) : (statements : List Stmt) →
    ((Stmt.listLinePieces indent statements).map tokensOf).flatten = Stmt.listTokens statements
  | [] => rfl
  | statement :: rest => by
      simp [Stmt.listLinePieces, Stmt.listTokens, Stmt.linePieces_tokens indent statement,
        Stmt.listLinePieces_tokens indent rest]

end

mutual

theorem Stmt.linePieces_separated (indent : Nat) : (statement : Stmt) →
    (∀ name ∈ statement.identifiers, ValidIdentifier name) →
    ∀ line ∈ statement.linePieces indent, Separated line
  | .letDecl identifier type initializer, valid, line, mem => by
      simp only [Stmt.linePieces, List.mem_singleton] at mem
      subst mem
      have initializerPart := Expr.separated_append initializer
        (fun name mem => valid name (by simp [Stmt.identifiers, mem])) [sym ';']
        (sym_valid (by decide)) (head_sym (by decide))
      have typePart := LocalType.separated_append type _ (Separated.cons_space
        (Separated.cons_equal (Separated.cons_space initializerPart)
          (fun next same => by cases same; rfl))) head_space
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
        (Separated.cons_space (Separated.cons_word (valid identifier (by simp [Stmt.identifiers]))
          (Separated.cons_sym (by decide) (Separated.cons_space typePart))
          (head_sym (by decide))))
        head_space)
  | .assign identifier value, valid, line, mem => by
      simp only [Stmt.linePieces, List.mem_singleton] at mem
      subst mem
      have valuePart := Expr.separated_append value
        (fun name mem => valid name (by simp [Stmt.identifiers, mem])) [sym ';']
        (sym_valid (by decide)) (head_sym (by decide))
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact Separated.blanks_append indent (Separated.cons_word
        (valid identifier (by simp [Stmt.identifiers]))
        (Separated.cons_space (Separated.cons_equal (Separated.cons_space valuePart)
          (fun next same => by cases same; rfl))) head_space)
  | .ifElse condition thenBlock elseBlock, valid, line, mem => by
      simp only [Stmt.linePieces, List.mem_append, List.mem_singleton] at mem
      rcases mem with (((same | mem) | same) | mem) | same
      · subst same
        have conditionPart := Expr.separated_append condition
          (fun name mem => valid name (by simp [Stmt.identifiers, mem]))
          [sym ')', space, sym '{'] (Separated.cons_sym (by decide) (Separated.cons_space
            (sym_valid (by decide)))) (head_sym (by decide))
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_space (Separated.cons_sym (by decide) conditionPart)) head_space)
      · exact Stmt.listLinePieces_separated (indent + 4) thenBlock
          (fun name mem => valid name (by simp [Stmt.identifiers, mem])) line mem
      · subst same
        exact Separated.blanks_append indent (Separated.cons_sym (by decide)
          (Separated.cons_space (Separated.cons_word (keyword_valid (by decide))
            (Separated.cons_space (sym_valid (by decide))) head_space)))
      · exact Stmt.listLinePieces_separated (indent + 4) elseBlock
          (fun name mem => valid name (by simp [Stmt.identifiers, mem])) line mem
      · subst same
        exact Separated.blanks_append indent (sym_valid (by decide))
  | .matchPair scrutinee first second body, valid, line, mem => by
      simp only [Stmt.linePieces, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      rcases mem with ((same | same) | mem) | same | same
      · subst same
        have scrutineePart := Expr.separated_append scrutinee
          (fun name mem => valid name (by simp [Stmt.identifiers, mem]))
          [sym ')', space, sym '{'] (Separated.cons_sym (by decide) (Separated.cons_space
            (sym_valid (by decide)))) (head_sym (by decide))
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_space (Separated.cons_sym (by decide) scrutineePart)) head_space)
      · subst same
        exact Separated.blanks_append (indent + 4) (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_space (Separated.cons_sym (by decide) (Separated.cons_word
            (valid first (by simp [Stmt.identifiers])) (Separated.cons_sym (by decide)
              (Separated.cons_space (Separated.cons_word (valid second (by simp [Stmt.identifiers]))
                (Separated.cons_sym (by decide) (Separated.cons_space (sym_valid (by decide))))
                (head_sym (by decide))))) (head_sym (by decide))))) head_space)
      · exact Stmt.listLinePieces_separated (indent + 8) body
          (fun name mem => valid name (by simp [Stmt.identifiers, mem])) line mem
      · subst same
        exact Separated.blanks_append (indent + 4) (sym_valid (by decide))
      · subst same
        exact Separated.blanks_append indent (sym_valid (by decide))
  | .matchSum scrutinee left leftBody right rightBody, valid, line, mem => by
      simp only [Stmt.linePieces, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      rcases mem with (((((same | same) | mem) | same | same) | mem) | same | same)
      · subst same
        have scrutineePart := Expr.separated_append scrutinee
          (fun name mem => valid name (by simp [Stmt.identifiers, mem]))
          [sym ')', space, sym '{'] (Separated.cons_sym (by decide) (Separated.cons_space
            (sym_valid (by decide)))) (head_sym (by decide))
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_space (Separated.cons_sym (by decide) scrutineePart)) head_space)
      · subst same
        exact Separated.blanks_append (indent + 4) (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_space (Separated.cons_word (keyword_valid (by decide))
            (Separated.cons_sym (by decide) (Separated.cons_word
              (valid left (by simp [Stmt.identifiers])) (Separated.cons_sym (by decide)
                (Separated.cons_space (sym_valid (by decide)))) (head_sym (by decide))))
            (head_sym (by decide)))) head_space)
      · exact Stmt.listLinePieces_separated (indent + 8) leftBody
          (fun name mem => valid name (by simp [Stmt.identifiers, mem])) line mem
      · subst same
        exact Separated.blanks_append (indent + 4) (sym_valid (by decide))
      · subst same
        exact Separated.blanks_append (indent + 4) (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_space (Separated.cons_word (keyword_valid (by decide))
            (Separated.cons_sym (by decide) (Separated.cons_word
              (valid right (by simp [Stmt.identifiers])) (Separated.cons_sym (by decide)
                (Separated.cons_space (sym_valid (by decide)))) (head_sym (by decide))))
            (head_sym (by decide)))) head_space)
      · exact Stmt.listLinePieces_separated (indent + 8) rightBody
          (fun name mem => valid name (by simp [Stmt.identifiers, mem])) line mem
      · subst same
        exact Separated.blanks_append (indent + 4) (sym_valid (by decide))
      · subst same
        exact Separated.blanks_append indent (sym_valid (by decide))

theorem Stmt.listLinePieces_separated (indent : Nat) : (statements : List Stmt) →
    (∀ name ∈ Stmt.listIdentifiers statements, ValidIdentifier name) →
    ∀ line ∈ Stmt.listLinePieces indent statements, Separated line
  | [], _, _, mem => by simp [Stmt.listLinePieces] at mem
  | statement :: rest, valid, line, mem => by
      simp only [Stmt.listLinePieces, List.mem_append] at mem
      rcases mem with mem | mem
      · exact Stmt.linePieces_separated indent statement
          (fun name found => valid name (by simp [Stmt.listIdentifiers, found])) line mem
      · exact Stmt.listLinePieces_separated indent rest
          (fun name found => valid name (by simp [Stmt.listIdentifiers, found])) line mem

end

/-! ### Files -/

def parameterPieces : List String → List Piece
  | [] => []
  | [parameter] => [word parameter, sym ':', space, word "uint256"]
  | parameter :: next :: rest =>
      [word parameter, sym ':', space, word "uint256", sym ',', space] ++
        parameterPieces (next :: rest)

theorem parameterText_toList : (parameters : List String) →
    (Method.parameterText parameters).toList = render (parameterPieces parameters)
  | [] => rfl
  | [parameter] => by
      simp [Method.parameterText, parameterPieces, render, Piece.chars, Token.chars, word, sym,
        space]
  | parameter :: next :: rest => by
      have tail := parameterText_toList (next :: rest)
      simp only [Method.parameterText, List.map_cons] at tail ⊢
      rw [String.intercalate_cons_cons, String.toList_append, String.toList_append, tail]
      simp [parameterPieces, render, Piece.chars, Token.chars, word, sym, space]

theorem parameterPieces_tokens : (parameters : List String) →
    tokensOf (parameterPieces parameters) = parameterTokens parameters
  | [] => rfl
  | [_] => rfl
  | parameter :: next :: rest => by
      simp [parameterPieces, parameterTokens, tokensOf, word, sym, space,
        parameterPieces_tokens (next :: rest)]

theorem parameterPieces_separated : (parameters : List String) →
    (∀ parameter ∈ parameters, ValidIdentifier parameter) →
    ∀ rest, Separated rest → (∀ next ∈ rest.head?, next.SafeLeft) →
    Separated (parameterPieces parameters ++ rest)
  | [], _, _, separated, _ => separated
  | [parameter], valid, rest, separated, safe => by
      simp only [parameterPieces, List.cons_append, List.nil_append]
      exact Separated.cons_word (valid parameter (by simp)) (Separated.cons_sym (by decide)
        (Separated.cons_space (Separated.cons_word (keyword_valid (by decide)) separated safe)))
        (head_sym (by decide))
  | parameter :: next :: more, valid, rest, separated, safe => by
      have tail := parameterPieces_separated (next :: more)
        (fun name mem => valid name (List.mem_cons_of_mem _ mem)) rest separated safe
      simp only [parameterPieces, List.cons_append, List.nil_append]
      exact Separated.cons_word (valid parameter (by simp)) (Separated.cons_sym (by decide)
        (Separated.cons_space (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_sym (by decide) (Separated.cons_space tail))
          (head_sym (by decide))))) (head_sym (by decide))

def typedParameterPieces : List (String × LocalType) → List Piece
  | [] => []
  | [parameter] => [word parameter.1, sym ':', space] ++ parameter.2.pieces
  | parameter :: next :: rest =>
      [word parameter.1, sym ':', space] ++ parameter.2.pieces ++ [sym ',', space] ++
        typedParameterPieces (next :: rest)

theorem typedParameterText_toList : (parameters : List (String × LocalType)) →
    (FunctionDecl.parameterText parameters).toList = render (typedParameterPieces parameters)
  | [] => rfl
  | [parameter] => by
      simp [FunctionDecl.parameterText, typedParameterPieces, render, Piece.chars,
        Token.chars, word, sym, space, LocalType.spelling_toList]
  | parameter :: next :: rest => by
      have tail := typedParameterText_toList (next :: rest)
      simp only [FunctionDecl.parameterText, List.map_cons] at tail ⊢
      rw [String.intercalate_cons_cons, String.toList_append, String.toList_append, tail]
      simp [typedParameterPieces, render, render_append, Piece.chars, Token.chars, word, sym,
        space, LocalType.spelling_toList]

theorem typedParameterPieces_tokens : (parameters : List (String × LocalType)) →
    tokensOf (typedParameterPieces parameters) = typedParameterTokens parameters
  | [] => rfl
  | [_] => by
      simp [typedParameterPieces, typedParameterTokens, tokensOf, word, sym, space,
        LocalType.tokensOf_pieces]
  | parameter :: next :: rest => by
      simp [typedParameterPieces, typedParameterTokens, tokensOf, tokensOf_append, word, sym,
        space, LocalType.tokensOf_pieces, typedParameterPieces_tokens (next :: rest)]

theorem typedParameterPieces_separated : (parameters : List (String × LocalType)) →
    (∀ parameter ∈ parameters, ValidIdentifier parameter.1) →
    ∀ rest, Separated rest → (∀ next ∈ rest.head?, next.SafeLeft) →
    Separated (typedParameterPieces parameters ++ rest)
  | [], _, _, separated, _ => separated
  | [parameter], valid, rest, separated, safe => by
      simp only [typedParameterPieces, List.cons_append, List.nil_append]
      exact Separated.cons_word (valid parameter (by simp)) (Separated.cons_sym (by decide)
        (Separated.cons_space (LocalType.separated_append _ _ separated safe)))
        (head_sym (by decide))
  | parameter :: next :: more, valid, rest, separated, safe => by
      have tail := typedParameterPieces_separated (next :: more)
        (fun name mem => valid name (List.mem_cons_of_mem _ mem)) rest separated safe
      simp only [typedParameterPieces, List.cons_append, List.nil_append, List.append_assoc]
      exact Separated.cons_word (valid parameter (by simp)) (Separated.cons_sym (by decide)
        (Separated.cons_space (LocalType.separated_append _ _
          (Separated.cons_sym (by decide) (Separated.cons_space tail))
          (head_sym (by decide))))) (head_sym (by decide))

/-- One piece list per printed line of a free function. -/
def FunctionDecl.linePieces (function : FunctionDecl) : List (List Piece) :=
  [[word "function", space, word function.name, sym '('] ++
      typedParameterPieces function.parameters ++
      [sym ')', space, word "returns", space, sym '('] ++ function.resultType.pieces ++
        [sym ')', space, sym '{']] ++
    Stmt.listLinePieces 4 function.body ++
    [blanks 4 ++ [word "return", space] ++ function.result.pieces ++ [sym ';'], [sym '}'], []]

theorem FunctionDecl.lines_toList (function : FunctionDecl) :
    function.lines.map String.toList = function.linePieces.map render := by
  simp [FunctionDecl.lines, FunctionDecl.linePieces, Stmt.listLines_toList,
    typedParameterText_toList, Expr.print_toList, render_append, render_blanks, render,
    Piece.chars, Token.chars, word, sym, space, LocalType.spelling_toList]

theorem FunctionDecl.linePieces_tokens (function : FunctionDecl) :
    (function.linePieces.map tokensOf).flatten = function.tokens := by
  simp [FunctionDecl.linePieces, FunctionDecl.tokens, Stmt.listLinePieces_tokens,
    typedParameterPieces_tokens, Expr.tokensOf_pieces, tokensOf_append, tokensOf_blanks,
    tokensOf, word, sym, space, LocalType.tokensOf_pieces]

theorem FunctionDecl.linePieces_separated (function : FunctionDecl)
    (valid : ∀ name ∈ function.identifiers, ValidIdentifier name) :
    ∀ line ∈ function.linePieces, Separated line := by
  have nameValid : ValidIdentifier function.name :=
    valid function.name (by simp [FunctionDecl.identifiers])
  have parametersValid : ∀ parameter ∈ function.parameters, ValidIdentifier parameter.1 :=
    fun parameter mem => valid parameter.1 (by
      simp only [FunctionDecl.identifiers]
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_map_of_mem mem))))
  have bodyValid : ∀ name ∈ Stmt.listIdentifiers function.body, ValidIdentifier name :=
    fun name mem => valid name (by simp [FunctionDecl.identifiers, mem])
  have resultValid : function.result.IdentifiersValid :=
    fun name mem => valid name (by simp [FunctionDecl.identifiers, mem])
  intro line mem
  simp only [FunctionDecl.linePieces, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at mem
  rcases mem with (same | mem) | same | same | same
  · subst same
    have parametersPart := typedParameterPieces_separated function.parameters parametersValid
      ([sym ')', space, word "returns", space, sym '('] ++ function.resultType.pieces ++
        [sym ')', space, sym '{'])
      (Separated.cons_sym (by decide) (Separated.cons_space (Separated.cons_word
        (keyword_valid (by decide)) (Separated.cons_space (Separated.cons_sym (by decide)
          (LocalType.separated_append _ _ (Separated.cons_sym (by decide)
            (Separated.cons_space (sym_valid (by decide)))) (head_sym (by decide)))))
        head_space)))
      (head_sym (by decide))
    simp only [List.cons_append, List.nil_append, List.append_assoc] at parametersPart ⊢
    exact Separated.cons_word (keyword_valid (by decide)) (Separated.cons_space
      (Separated.cons_word nameValid (Separated.cons_sym (by decide) parametersPart)
        (head_sym (by decide)))) head_space
  · exact Stmt.listLinePieces_separated 4 function.body bodyValid line mem
  · subst same
    have resultPart := Expr.separated_append function.result resultValid [sym ';']
      (sym_valid (by decide)) (head_sym (by decide))
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact Separated.blanks_append 4 (Separated.cons_word (keyword_valid (by decide))
      (Separated.cons_space resultPart) head_space)
  · subst same
    exact sym_valid (by decide)
  · subst same
    trivial

def aliasPieces : List (String × String) → List Piece
  | [] => []
  | [alias] => [word alias.1, space, word "as", space, word alias.2]
  | alias :: next :: rest =>
      [word alias.1, space, word "as", space, word alias.2, sym ',', space] ++
        aliasPieces (next :: rest)

theorem aliasText_toList : (aliases : List (String × String)) →
    (String.intercalate ", " (aliases.map fun alias => alias.1 ++ " as " ++ alias.2)).toList =
      render (aliasPieces aliases)
  | [] => rfl
  | [alias] => by
      simp [aliasPieces, render, Piece.chars, Token.chars, word, space]
  | alias :: next :: rest => by
      have tail := aliasText_toList (next :: rest)
      simp only [List.map_cons] at tail ⊢
      rw [String.intercalate_cons_cons, String.toList_append, String.toList_append, tail]
      simp [aliasPieces, render, Piece.chars, Token.chars, word, sym, space]

theorem aliasPieces_tokens : (aliases : List (String × String)) →
    tokensOf (aliasPieces aliases) = aliasTokens aliases
  | [] => rfl
  | [_] => rfl
  | alias :: next :: rest => by
      simp [aliasPieces, aliasTokens, tokensOf, word, sym, space,
        aliasPieces_tokens (next :: rest)]

theorem aliasPieces_separated : (aliases : List (String × String)) →
    (∀ alias ∈ aliases, ValidIdentifier alias.1 ∧ ValidIdentifier alias.2) →
    ∀ rest, Separated rest → (∀ next ∈ rest.head?, next.SafeLeft) →
    Separated (aliasPieces aliases ++ rest)
  | [], _, _, separated, _ => separated
  | [alias], valid, rest, separated, safe => by
      obtain ⟨opcodeValid, aliasValid⟩ := valid alias (by simp)
      simp only [aliasPieces, List.cons_append, List.nil_append]
      exact Separated.cons_word opcodeValid (Separated.cons_space (Separated.cons_word
        (keyword_valid (by decide)) (Separated.cons_space (Separated.cons_word aliasValid
          separated safe)) head_space)) head_space
  | alias :: next :: more, valid, rest, separated, safe => by
      obtain ⟨opcodeValid, aliasValid⟩ := valid alias (by simp)
      have tail := aliasPieces_separated (next :: more)
        (fun other mem => valid other (List.mem_cons_of_mem _ mem)) rest separated safe
      simp only [aliasPieces, List.cons_append, List.nil_append]
      exact Separated.cons_word opcodeValid (Separated.cons_space (Separated.cons_word
        (keyword_valid (by decide)) (Separated.cons_space (Separated.cons_word aliasValid
          (Separated.cons_sym (by decide) (Separated.cons_space tail))
          (head_sym (by decide)))) head_space)) head_space

def aliasImportLinePieces : List (String × String) → List (List Piece)
  | [] => []
  | alias :: rest =>
      [[word "import", space, sym '{', space] ++ aliasPieces (alias :: rest) ++
        [space, sym '}', space, word "from", space, word "std", sym '.', word "opcodes",
          sym ';']]

theorem aliasImportLines_toList (aliases : List (String × String)) :
    (aliasImportLines aliases).map String.toList = (aliasImportLinePieces aliases).map render := by
  cases aliases with
  | nil => rfl
  | cons alias rest =>
      simp only [aliasImportLines, aliasImportLinePieces, List.map_cons, List.map_nil,
        List.cons.injEq, and_true]
      rw [aliasImportLine, String.toList_append, String.toList_append, aliasText_toList]
      simp [render_append, render, Piece.chars, Token.chars, word, sym, space]

theorem aliasImportLinePieces_tokens (aliases : List (String × String)) :
    ((aliasImportLinePieces aliases).map tokensOf).flatten = aliasImportTokens aliases := by
  cases aliases with
  | nil => rfl
  | cons alias rest =>
      simp [aliasImportLinePieces, aliasImportTokens, tokensOf_append, aliasPieces_tokens,
        tokensOf, word, sym, space]

theorem aliasImportLinePieces_separated (aliases : List (String × String))
    (valid : ∀ alias ∈ aliases, ValidIdentifier alias.1 ∧ ValidIdentifier alias.2) :
    ∀ line ∈ aliasImportLinePieces aliases, Separated line := by
  cases aliases with
  | nil => intro line mem; cases mem
  | cons alias rest =>
      intro line mem
      simp only [aliasImportLinePieces, List.mem_singleton] at mem
      subst mem
      have aliasesPart := aliasPieces_separated (alias :: rest) valid
        [space, sym '}', space, word "from", space, word "std", sym '.', word "opcodes", sym ';']
        (Separated.cons_space (Separated.cons_sym (by decide) (Separated.cons_space
          (Separated.cons_word (keyword_valid (by decide)) (Separated.cons_space
            (Separated.cons_word (keyword_valid (by decide)) (Separated.cons_sym (by decide)
              (Separated.cons_word (keyword_valid (by decide)) (sym_valid (by decide))
                (head_sym (by decide)))) (head_sym (by decide)))) head_space))))
        head_space
      simp only [List.cons_append, List.nil_append]
      exact Separated.cons_word (keyword_valid (by decide)) (Separated.cons_space
        (Separated.cons_sym (by decide) (Separated.cons_space aliasesPart))) head_space

def SourceFile.linePieces (file : SourceFile) : List (List Piece) :=
  [[word "pragma", space, word "solcore", sym ';'],
    [word "import", space, sym '*', space, word "from", space, word "std", sym ';'],
    [word "import", space, sym '*', space, word "from", space, word "std", sym '.',
      word "dispatch", sym ';']] ++
  aliasImportLinePieces file.opcodeAliases ++ [[]] ++
  file.functions.flatMap FunctionDecl.linePieces ++
  [[word "contract", space, word file.contract, space, sym '{'],
    blanks 4 ++ [word "function", space, word file.method.name, sym '('] ++
      parameterPieces file.method.parameters ++
      [sym ')', space, word "public", space, word "returns", space, sym '(', word "uint256",
        sym ')', space, sym '{']] ++
  Stmt.listLinePieces 8 file.method.body ++
  [blanks 8 ++ [word "return", space] ++ file.method.result.pieces ++ [sym ';'],
    blanks 4 ++ [sym '}'], [sym '}']]

theorem functions_lines_toList (functions : List FunctionDecl) :
    (functions.flatMap FunctionDecl.lines).map String.toList =
      (functions.flatMap FunctionDecl.linePieces).map render := by
  induction functions with
  | nil => rfl
  | cons function rest ih =>
      simp only [List.flatMap_cons, List.map_append, ih, FunctionDecl.lines_toList]

theorem functions_linePieces_tokens (functions : List FunctionDecl) :
    ((functions.flatMap FunctionDecl.linePieces).map tokensOf).flatten =
      functions.flatMap FunctionDecl.tokens := by
  induction functions with
  | nil => rfl
  | cons function rest ih =>
      simp only [List.flatMap_cons, List.map_append, List.flatten_append, ih,
        FunctionDecl.linePieces_tokens]

theorem SourceFile.lines_toList (file : SourceFile) :
    file.lines.map String.toList = file.linePieces.map render := by
  simp only [SourceFile.lines, SourceFile.linePieces, List.map_append, aliasImportLines_toList,
    functions_lines_toList]
  simp [Stmt.listLines_toList, parameterText_toList, Expr.print_toList, render_append,
    render_blanks, render, Piece.chars, Token.chars, word, sym, space]

theorem SourceFile.linePieces_tokens (file : SourceFile) :
    (file.linePieces.map tokensOf).flatten = file.tokens := by
  simp only [SourceFile.linePieces, SourceFile.tokens, List.map_append, List.flatten_append,
    aliasImportLinePieces_tokens, functions_linePieces_tokens]
  simp [importTokens, signatureTokens, Stmt.listLinePieces_tokens, parameterPieces_tokens,
    Expr.tokensOf_pieces, tokensOf_append, tokensOf_blanks, tokensOf, word, sym, space]

/-- Every identifier of the file is lexically valid. -/
def SourceFile.IdentifiersValid (file : SourceFile) : Prop :=
  (∀ alias ∈ file.opcodeAliases, ValidIdentifier alias.1 ∧ ValidIdentifier alias.2) ∧
    (∀ function ∈ file.functions, ∀ name ∈ function.identifiers, ValidIdentifier name) ∧
    ValidIdentifier file.contract ∧ ValidIdentifier file.method.name ∧
    (∀ parameter ∈ file.method.parameters, ValidIdentifier parameter) ∧
    (∀ name ∈ Stmt.listIdentifiers file.method.body, ValidIdentifier name) ∧
    (∀ name ∈ file.method.result.identifiers, ValidIdentifier name)

theorem SourceFile.linePieces_separated (file : SourceFile) (valid : file.IdentifiersValid) :
    ∀ line ∈ file.linePieces, Separated line := by
  obtain ⟨aliasesValid, functionsValid, contractValid, methodValid, parametersValid, bodyValid,
    resultValid⟩ := valid
  intro line mem
  simp only [SourceFile.linePieces, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_flatMap] at mem
  rcases mem with ((((((same | same | same) | mem) | same) | ⟨function, functionMem, mem⟩) |
    (same | same)) | mem) | (same | same | same)
  · subst same
    exact Separated.cons_word (keyword_valid (by decide)) (Separated.cons_space
      (Separated.cons_word (keyword_valid (by decide)) (sym_valid (by decide))
        (head_sym (by decide)))) head_space
  · subst same
    exact Separated.cons_word (keyword_valid (by decide)) (Separated.cons_space
      (Separated.cons_sym (by decide) (Separated.cons_space (Separated.cons_word
        (keyword_valid (by decide)) (Separated.cons_space (Separated.cons_word
          (keyword_valid (by decide)) (sym_valid (by decide)) (head_sym (by decide))))
        head_space)))) head_space
  · subst same
    exact Separated.cons_word (keyword_valid (by decide)) (Separated.cons_space
      (Separated.cons_sym (by decide) (Separated.cons_space (Separated.cons_word
        (keyword_valid (by decide)) (Separated.cons_space (Separated.cons_word
          (keyword_valid (by decide)) (Separated.cons_sym (by decide) (Separated.cons_word
            (keyword_valid (by decide)) (sym_valid (by decide)) (head_sym (by decide))))
          (head_sym (by decide)))) head_space)))) head_space
  · exact aliasImportLinePieces_separated file.opcodeAliases aliasesValid line mem
  · subst same
    trivial
  · exact FunctionDecl.linePieces_separated function (functionsValid function functionMem) line
      mem
  · subst same
    exact Separated.cons_word (keyword_valid (by decide)) (Separated.cons_space
      (Separated.cons_word contractValid (Separated.cons_space (sym_valid (by decide)))
        head_space)) head_space
  · subst same
    have parametersPart := parameterPieces_separated file.method.parameters parametersValid
      [sym ')', space, word "public", space, word "returns", space, sym '(', word "uint256",
        sym ')', space, sym '{']
      (Separated.cons_sym (by decide) (Separated.cons_space (Separated.cons_word
        (keyword_valid (by decide)) (Separated.cons_space (Separated.cons_word
          (keyword_valid (by decide)) (Separated.cons_space (Separated.cons_sym (by decide)
            (Separated.cons_word (keyword_valid (by decide)) (Separated.cons_sym (by decide)
              (Separated.cons_space (sym_valid (by decide)))) (head_sym (by decide)))))
          head_space)) head_space)))
      (head_sym (by decide))
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact Separated.blanks_append 4 (Separated.cons_word (keyword_valid (by decide))
      (Separated.cons_space (Separated.cons_word methodValid (Separated.cons_sym (by decide)
        parametersPart) (head_sym (by decide)))) head_space)
  · exact Stmt.listLinePieces_separated 8 file.method.body bodyValid line mem
  · subst same
    have resultPart := Expr.separated_append file.method.result resultValid [sym ';']
      (sym_valid (by decide)) (head_sym (by decide))
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact Separated.blanks_append 8 (Separated.cons_word (keyword_valid (by decide))
      (Separated.cons_space resultPart) head_space)
  · subst same
    exact Separated.blanks_append 4 (sym_valid (by decide))
  · subst same
    exact sym_valid (by decide)

/-! ### Joining lines -/

def newline : Piece := .blank '\n'

def joinLines (lines : List (List Piece)) : List Piece :=
  List.intercalate [newline] lines ++ [newline]

theorem render_intercalate : (lines : List (List Piece)) →
    render (List.intercalate [newline] lines) = List.intercalate ['\n'] (lines.map render)
  | [] => rfl
  | [_] => by simp
  | line :: next :: rest => by
      rw [List.intercalate_cons_cons, render_append, render_append, render_intercalate (next :: rest)]
      simp [render, Piece.chars, newline]

theorem tokensOf_joinLines : (lines : List (List Piece)) →
    tokensOf (joinLines lines) = (lines.map tokensOf).flatten
  | [] => rfl
  | [line] => by simp [joinLines, tokensOf_append, tokensOf, newline]
  | line :: next :: rest => by
      have tail := tokensOf_joinLines (next :: rest)
      have newlineTokens : tokensOf [newline] = [] := rfl
      simp only [joinLines, List.intercalate_cons_cons, tokensOf_append, newlineTokens,
        List.append_nil] at tail ⊢
      rw [tail]
      simp

theorem newline_valid : newline.Valid := rfl
theorem newline_safeLeft : newline.SafeLeft := ⟨rfl, rfl⟩
theorem newline_safeRight : newline.SafeRight := ⟨rfl, by simp [newline]⟩

theorem joinLines_separated : (lines : List (List Piece)) →
    (∀ line ∈ lines, Separated line) → Separated (joinLines lines)
  | [], _ => newline_valid
  | [line], all => by
      simp only [joinLines, List.intercalate_singleton]
      exact Separated.append_before (all line (by simp)) newline_valid
        (fun next same => by cases same; exact newline_safeLeft)
  | line :: next :: rest, all => by
      have tail := joinLines_separated (next :: rest)
        (fun other mem => all other (List.mem_cons_of_mem _ mem))
      simp only [joinLines] at tail ⊢
      rw [List.intercalate_cons_cons]
      simp only [List.append_assoc]
      exact Separated.append_before (all line (by simp))
        (Separated.cons_safe (by simpa using newline_valid) newline_safeRight tail)
        (fun next same => by cases same; exact newline_safeLeft)

theorem SourceFile.print_toList (file : SourceFile) :
    file.print.toList = render (joinLines file.linePieces) := by
  rw [SourceFile.print, String.toList_append, String.toList_intercalate, joinLines, render_append,
    render_intercalate, SourceFile.lines_toList]
  rfl

/-- **Text round trip.** The printed text of a file with lexically valid,
non-reserved names parses back to that file. -/
theorem parseSource_print (file : SourceFile) (names : file.NamesOk)
    (valid : file.IdentifiersValid) : parseSource file.print = some file := by
  rw [parseSource, SourceFile.print_toList,
    lex_render (joinLines_separated _ (file.linePieces_separated valid)), Option.bind_some,
    tokensOf_joinLines, SourceFile.linePieces_tokens]
  exact parseFile_tokens file names

/-- The meaning of a printed file's text is the meaning of the file. -/
theorem sourceCall_print (file : SourceFile) (names : file.NamesOk)
    (valid : file.IdentifiersValid) (method : String) (arguments : List Nat) :
    sourceCall file.print method arguments = file.call method arguments := by
  simp [sourceCall, parseSource_print file names valid]

end Solcore.Synthesis.Source.ScalarMeaning
end
