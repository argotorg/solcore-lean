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

theorem LocalType.spelling_valid (type : LocalType) : ValidIdentifier type.spelling := by
  cases type
  · exact keyword_valid (by decide)
  · exact keyword_valid (by decide)

/-! ### Statements -/

mutual

def Stmt.linePieces (indent : Nat) : Stmt → List (List Piece)
  | .letDecl identifier type initializer =>
      [blanks indent ++ [word "let", space, word identifier, sym ':', space, word type.spelling,
        space, sym '=', space] ++ initializer.pieces ++ [sym ';']]
  | .assign identifier value =>
      [blanks indent ++ [word identifier, space, sym '=', space] ++ value.pieces ++ [sym ';']]
  | .ifElse condition thenBlock elseBlock =>
      [blanks indent ++ [word "if", space, sym '('] ++ condition.pieces ++
          [sym ')', space, sym '{']] ++
        Stmt.listLinePieces (indent + 4) thenBlock ++
        [blanks indent ++ [sym '}', space, word "else", space, sym '{']] ++
        Stmt.listLinePieces (indent + 4) elseBlock ++ [blanks indent ++ [sym '}']]

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
        Piece.chars, Token.chars, word, sym, space, Expr.print_toList]
  | .assign identifier value => by
      simp [Stmt.lines, Stmt.linePieces, indentLine_toList, render_append, render_blanks, render,
        Piece.chars, Token.chars, word, sym, space, Expr.print_toList]
  | .ifElse condition thenBlock elseBlock => by
      simp [Stmt.lines, Stmt.linePieces, indentLine_toList, render_append, render_blanks, render,
        Piece.chars, Token.chars, word, sym, space, Expr.print_toList,
        Stmt.listLines_toList (indent + 4) thenBlock, Stmt.listLines_toList (indent + 4) elseBlock]

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
        space, Expr.tokensOf_pieces]
  | .assign identifier value => by
      simp [Stmt.linePieces, Stmt.tokens, tokensOf_append, tokensOf_blanks, tokensOf, word, sym,
        space, Expr.tokensOf_pieces]
  | .ifElse condition thenBlock elseBlock => by
      simp [Stmt.linePieces, Stmt.tokens, tokensOf_append, tokensOf_blanks, tokensOf, word, sym,
        space, Expr.tokensOf_pieces, Stmt.listLinePieces_tokens (indent + 4) thenBlock,
        Stmt.listLinePieces_tokens (indent + 4) elseBlock]

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
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
        (Separated.cons_space (Separated.cons_word (valid identifier (by simp [Stmt.identifiers]))
          (Separated.cons_sym (by decide) (Separated.cons_space (Separated.cons_word
            (LocalType.spelling_valid type) (Separated.cons_space (Separated.cons_equal
              (Separated.cons_space initializerPart) (fun next same => by cases same; rfl)))
            head_space))) (head_sym (by decide))))
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

def SourceFile.linePieces (file : SourceFile) : List (List Piece) :=
  [[word "import", space, sym '*', space, word "from", space, word "std", sym ';'],
    [word "import", space, sym '*', space, word "from", space, word "std", sym '.',
      word "dispatch", sym ';'],
    [],
    [word "contract", space, word file.contract, space, sym '{'],
    blanks 4 ++ [word "function", space, word file.method.name, sym '('] ++
      parameterPieces file.method.parameters ++
      [sym ')', space, word "public", space, word "returns", space, sym '(', word "uint256",
        sym ')', space, sym '{']] ++
  Stmt.listLinePieces 8 file.method.body ++
  [blanks 8 ++ [word "return", space] ++ file.method.result.pieces ++ [sym ';'],
    blanks 4 ++ [sym '}'], [sym '}']]

theorem SourceFile.lines_toList (file : SourceFile) :
    file.lines.map String.toList = file.linePieces.map render := by
  simp [SourceFile.lines, SourceFile.linePieces, Stmt.listLines_toList, parameterText_toList,
    Expr.print_toList, render_append, render_blanks, render, Piece.chars, Token.chars, word, sym,
    space]

theorem SourceFile.linePieces_tokens (file : SourceFile) :
    (file.linePieces.map tokensOf).flatten = file.tokens := by
  simp [SourceFile.linePieces, SourceFile.tokens, headerTokens, signatureTokens,
    Stmt.listLinePieces_tokens, parameterPieces_tokens, Expr.tokensOf_pieces, tokensOf_append,
    tokensOf_blanks, tokensOf, word, sym, space]

/-- Every identifier of the file is lexically valid. -/
def SourceFile.IdentifiersValid (file : SourceFile) : Prop :=
  ValidIdentifier file.contract ∧ ValidIdentifier file.method.name ∧
    (∀ parameter ∈ file.method.parameters, ValidIdentifier parameter) ∧
    (∀ name ∈ Stmt.listIdentifiers file.method.body, ValidIdentifier name) ∧
    (∀ name ∈ file.method.result.identifiers, ValidIdentifier name)

theorem SourceFile.linePieces_separated (file : SourceFile) (valid : file.IdentifiersValid) :
    ∀ line ∈ file.linePieces, Separated line := by
  obtain ⟨contractValid, methodValid, parametersValid, bodyValid, resultValid⟩ := valid
  intro line mem
  simp only [SourceFile.linePieces, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at mem
  rcases mem with ((same | same | same | same | same) | mem) | (same | same | same)
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
  · subst same
    trivial
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
