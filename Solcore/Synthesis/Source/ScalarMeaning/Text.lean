import Solcore.Synthesis.Source.ScalarMeaning.Parse
import Solcore.Synthesis.Source.ScalarMeaning.Print
import Solcore.Synthesis.Source.ScalarMeaning.Semantics

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
  [[word "import", space, sym '*', space, word "from", space, word "std", sym ';'],
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
  rcases mem with ((((((same | same) | mem) | same) | ⟨function, functionMem, mem⟩) |
    (same | same)) | mem) | (same | same | same)
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
