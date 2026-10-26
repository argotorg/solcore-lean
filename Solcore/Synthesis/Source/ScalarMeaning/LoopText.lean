import Solcore.Synthesis.Source.ScalarMeaning.LoopSemantics
import Solcore.Synthesis.Source.ScalarMeaning.Text

/-! Text of loop programs. `parseLoopSource` lexes a complete text as
`parseSource` does and parses it with the same grammar, except that a method
body statement may also be `while (left op right) { .. }`. Its tokens are
`while`, those of the parenthesized infix operation and those of the block. No
loop-free statement starts with the tokens `while (`, since an assignment to a
name `while` goes on with `=`. So every text that `parseSource` accepts is
accepted here as the same file, and `loopSourceCall` agrees with `sourceCall`
on it for every fuel. The printed text of every loop file with valid,
non-reserved names parses back to that file. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

/-! ### Tokens and parser -/

def LoopStmt.tokens : LoopStmt → List Token
  | .plain statement => statement.tokens
  | .whileLoop op left right body =>
      [.ident "while"] ++ (Expr.binary op left right).tokens ++ [.symbol '{'] ++
        Stmt.listTokens body ++ [.symbol '}']

def LoopStmt.listTokens : List LoopStmt → List Token
  | [] => []
  | statement :: rest => statement.tokens ++ LoopStmt.listTokens rest

def LoopFile.tokens (file : LoopFile) : List Token :=
  importTokens ++ aliasImportTokens file.opcodeAliases ++
    file.functions.flatMap FunctionDecl.tokens ++
    [.ident "contract", .ident file.contract, .symbol '{', .ident "function",
      .ident file.method.name, .symbol '('] ++ parameterTokens file.method.parameters ++
    signatureTokens ++ LoopStmt.listTokens file.method.body ++ [.ident "return"] ++
    file.method.result.tokens ++ [.symbol ';', .symbol '}', .symbol '}']

/-- The tokens that start a loop. -/
def whileTokens : List Token := [.ident "while", .symbol '(']

/-- Method body statements up to `return`: a loop where the tokens start with
`while (`, otherwise a loop-free statement. A loop's condition is the
expression from its `(`, which must be an infix operation. -/
def parseLoopStmts : Nat → List Token → Option (List LoopStmt × List Token)
  | 0, _ => none
  | fuel + 1, tokens =>
      if blockEnds tokens then some ([], tokens)
      else if tokens.take 2 = whileTokens then do
        let (condition, rest) ← parseExpr fuel (tokens.drop 1)
        match condition with
        | .binary op left right => do
            let rest ← expectTokens [.symbol '{'] rest
            let (body, rest) ← parseStmts fuel rest
            let rest ← expectTokens [.symbol '}'] rest
            let (statements, rest) ← parseLoopStmts fuel rest
            some (.whileLoop op left right body :: statements, rest)
        | _ => none
      else do
        let (statement, rest) ← parseStmt fuel tokens
        let (statements, rest) ← parseLoopStmts fuel rest
        some (.plain statement :: statements, rest)

/-- `parseFileWith` with a loop method body. -/
def parseLoopFileWith (fuel : Nat) (tokens : List Token) : Option LoopFile := do
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
  let (body, rest) ← parseLoopStmts fuel rest
  let rest ← expectTokens [.ident "return"] rest
  let (result, rest) ← parseExpr fuel rest
  let rest ← expectTokens [.symbol ';', .symbol '}', .symbol '}'] rest
  if rest = [] then some ⟨opcodeAliases, functions, contract, ⟨method, parameters, body, result⟩⟩
  else none

/-- Parse a complete token stream; one more than its length bounds nesting. -/
def parseLoopFile (tokens : List Token) : Option LoopFile :=
  parseLoopFileWith (tokens.length + 1) tokens

def parseLoopSource (source : String) : Option LoopFile :=
  (lex source.toList).bind parseLoopFile

/-- The returned ABI word of calling `method` on the contract written in
`source` when each loop may evaluate its condition at most `fuel` times. -/
def loopSourceCall (fuel : Nat) (source : String) (method : String) (arguments : List Nat) :
    Option Nat :=
  (parseLoopSource source).bind fun file => file.call fuel method arguments

/-- More fuel keeps the result of a completed call. -/
theorem loopSourceCall_mono {source method : String} {arguments : List Nat}
    {fuel more result : Nat} (enough : fuel ≤ more)
    (called : loopSourceCall fuel source method arguments = some result) :
    loopSourceCall more source method arguments = some result := by
  unfold loopSourceCall at called ⊢
  cases parsed : parseLoopSource source with
  | none => simp [parsed] at called
  | some file =>
      simp only [parsed, Option.bind_some] at called ⊢
      exact LoopFile.call_mono enough called

/-- All completed calls of a text return the same word. -/
theorem loopSourceCall_unique {source method : String} {arguments : List Nat}
    {first second firstResult secondResult : Nat}
    (firstCall : loopSourceCall first source method arguments = some firstResult)
    (secondCall : loopSourceCall second source method arguments = some secondResult) :
    firstResult = secondResult := by
  have left := loopSourceCall_mono (Nat.le_max_left first second) firstCall
  have right := loopSourceCall_mono (Nat.le_max_right first second) secondCall
  rw [left] at right
  exact Option.some.inj right

/-! ### Loop-free texts -/

theorem parseStmt_while (fuel : Nat) (more : List Token) :
    parseStmt fuel (.ident "while" :: .symbol '(' :: more) = none := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [parseStmt, isReserved, reservedWords, expectTokens]

/-- No loop-free statement starts with `while (`. -/
theorem parseStmt_not_while {fuel : Nat} {tokens rest : List Token} {statement : Stmt}
    (parsed : parseStmt fuel tokens = some (statement, rest)) : tokens.take 2 ≠ whileTokens := by
  intro starts
  match tokens with
  | [] => simp [whileTokens] at starts
  | [_] => simp [whileTokens] at starts
  | first :: second :: more =>
      simp only [List.take, whileTokens, List.cons.injEq, and_true] at starts
      obtain ⟨rfl, rfl⟩ := starts
      rw [parseStmt_while] at parsed
      cases parsed

theorem parseLoopStmts_of_parseStmts : ∀ (fuel : Nat) {tokens rest : List Token}
    {statements : List Stmt}, parseStmts fuel tokens = some (statements, rest) →
    parseLoopStmts fuel tokens = some (statements.map .plain, rest)
  | 0, _, _, _, parsed => by simp [parseStmts] at parsed
  | fuel + 1, tokens, rest, statements, parsed => by
      unfold parseStmts at parsed
      unfold parseLoopStmts
      by_cases ends : blockEnds tokens = true
      · rw [if_pos ends] at parsed ⊢
        simp only [Option.some.injEq, Prod.mk.injEq] at parsed
        obtain ⟨rfl, rfl⟩ := parsed
        rfl
      · rw [if_neg ends] at parsed ⊢
        cases statementParse : parseStmt fuel tokens with
        | none => simp [statementParse] at parsed
        | some pair =>
            obtain ⟨statement, middle⟩ := pair
            rw [if_neg (parseStmt_not_while statementParse)]
            simp only [statementParse, Option.bind_eq_bind, Option.bind_some] at parsed ⊢
            cases restParse : parseStmts fuel middle with
            | none => simp [restParse] at parsed
            | some pair =>
                obtain ⟨tail, final⟩ := pair
                simp only [restParse, Option.bind_some, Option.some.injEq,
                  Prod.mk.injEq] at parsed
                obtain ⟨rfl, rfl⟩ := parsed
                simp [parseLoopStmts_of_parseStmts fuel restParse]

theorem parseLoopFileWith_of_parseFileWith {fuel : Nat} {tokens : List Token}
    {file : SourceFile} (parsed : parseFileWith fuel tokens = some file) :
    parseLoopFileWith fuel tokens = some file.toLoop := by
  simp only [parseFileWith, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists]
    at parsed
  obtain ⟨rest₁, imports, aliases, rest₂, aliasesParse, functions, rest₃, functionsParse,
    rest₄, contractKeyword, contract, rest₅, contractParse, rest₆, functionKeyword, method,
    rest₇, methodParse, rest₈, opening, parameters, rest₉, parametersParse, rest₁₀, signature,
    body, rest₁₁, bodyParse, rest₁₂, returnKeyword, result, rest₁₃, resultParse, rest₁₄,
    closing, final⟩ := parsed
  by_cases empty : rest₁₄ = []
  · rw [if_pos empty] at final
    simp only [Option.some.injEq] at final
    subst final
    simp [parseLoopFileWith, imports, aliasesParse, functionsParse, contractKeyword,
      contractParse, functionKeyword, methodParse, opening, parametersParse, signature,
      parseLoopStmts_of_parseStmts fuel bodyParse, returnKeyword, resultParse, closing, empty,
      SourceFile.toLoop]
  · rw [if_neg empty] at final
    cases final

theorem parseLoopSource_of_parseSource {source : String} {file : SourceFile}
    (parsed : parseSource source = some file) : parseLoopSource source = some file.toLoop := by
  unfold parseSource at parsed
  unfold parseLoopSource
  cases lexed : lex source.toList with
  | none => simp [lexed] at parsed
  | some tokens =>
      simp only [lexed, Option.bind_some] at parsed ⊢
      exact parseLoopFileWith_of_parseFileWith parsed

/-- **Agreement on loop-free texts.** On every text that `parseSource`
accepts, the loop meaning is `sourceCall`, for every fuel. -/
theorem loopSourceCall_of_parseSource {source : String} {file : SourceFile}
    (parsed : parseSource source = some file) (fuel : Nat) (method : String)
    (arguments : List Nat) :
    loopSourceCall fuel source method arguments = sourceCall source method arguments := by
  simp [loopSourceCall, sourceCall, parseLoopSource_of_parseSource parsed, parsed,
    SourceFile.toLoop_call]

/-! ### Parser round trip -/

def LoopStmt.size : LoopStmt → Nat
  | .plain statement => statement.size
  | .whileLoop op left right body => (Expr.binary op left right).size + Stmt.listSize body + 1

def LoopStmt.listSize : List LoopStmt → Nat
  | [] => 0
  | statement :: rest => statement.size + LoopStmt.listSize rest + 1

def LoopStmt.ListNamesOk (statements : List LoopStmt) : Prop :=
  ∀ name ∈ LoopStmt.listIdentifiers statements, isReserved name = false

theorem Stmt.tokens_not_while (statement : Stmt) (rest : List Token) :
    (statement.tokens ++ rest).take 2 ≠ whileTokens := by
  cases statement <;> simp [Stmt.tokens, whileTokens]

theorem parseLoopStmts_tokens : ∀ (statements : List LoopStmt) (fuel : Nat) (rest : List Token),
    LoopStmt.ListNamesOk statements → LoopStmt.listSize statements < fuel →
    blockEnds rest = true →
    parseLoopStmts fuel (LoopStmt.listTokens statements ++ rest) = some (statements, rest)
  | [], fuel + 1, rest, _, _, ends => by simp [LoopStmt.listTokens, parseLoopStmts, ends]
  | .plain statement :: tail, fuel + 1, rest, names, enough, ends => by
      have statementNames : statement.NamesOk := fun name mem =>
        names name (by simp [LoopStmt.listIdentifiers, LoopStmt.identifiers, mem])
      have statementParse := (parseStmt_tokens_all fuel).1 statement
        (LoopStmt.listTokens tail ++ rest) statementNames
        (by simp only [LoopStmt.listSize, LoopStmt.size] at enough; omega)
      have tailParse := parseLoopStmts_tokens tail fuel rest
        (fun name mem => names name (by simp [LoopStmt.listIdentifiers, mem]))
        (by simp only [LoopStmt.listSize] at enough; omega) ends
      simp only [LoopStmt.listTokens, LoopStmt.tokens, List.append_assoc]
      rw [parseLoopStmts, if_neg (by rw [Stmt.blockEnds_tokens statement statementNames]; simp),
        if_neg (Stmt.tokens_not_while statement _)]
      simp [statementParse, tailParse]
  | .whileLoop op left right body :: tail, fuel + 1, rest, names, enough, ends => by
      have tailParse := parseLoopStmts_tokens tail fuel rest
        (fun name mem => names name (by simp [LoopStmt.listIdentifiers, mem]))
        (by simp only [LoopStmt.listSize] at enough; omega) ends
      have bodyParse := parseStmts_tokens (statements := body) (fuel := fuel)
        (rest := [.symbol '}'] ++ (LoopStmt.listTokens tail ++ rest))
        (fun name mem => names name (by
          simp [LoopStmt.listIdentifiers, LoopStmt.identifiers, mem]))
        (by simp only [LoopStmt.listSize, LoopStmt.size] at enough; omega) rfl
      have conditionNames : (Expr.binary op left right).NamesOk := fun name mem =>
        names name (by
          simp only [Expr.identifiers, List.mem_append] at mem
          simp only [LoopStmt.listIdentifiers, LoopStmt.identifiers, List.mem_append]
          rcases mem with mem | mem <;> simp [mem])
      have conditionParse := parseExpr_tokens (.binary op left right) fuel
        ([.symbol '{'] ++ Stmt.listTokens body ++ [.symbol '}'] ++
          (LoopStmt.listTokens tail ++ rest)) conditionNames
        (by simp only [LoopStmt.listSize, LoopStmt.size] at enough; omega) (by simp)
      simp only [List.cons_append, List.nil_append] at bodyParse
      simp only [Expr.tokens, List.append_assoc, List.cons_append, List.nil_append]
        at conditionParse
      simp only [LoopStmt.listTokens, LoopStmt.tokens, Expr.tokens, List.append_assoc,
        List.cons_append, List.nil_append]
      simp [parseLoopStmts, blockEnds, whileTokens, conditionParse, expectTokens, bodyParse,
        tailParse]
  | _, 0, _, _, enough, _ => absurd enough (Nat.not_lt_zero _)

theorem LoopStmt.listSize_le_tokens : (statements : List LoopStmt) →
    LoopStmt.listSize statements ≤ (LoopStmt.listTokens statements).length
  | [] => by simp [LoopStmt.listSize, LoopStmt.listTokens]
  | .plain statement :: rest => by
      have := (Stmt.size_bounds (statement.size + 1)).1 statement (Nat.lt_succ_self _)
      have := LoopStmt.listSize_le_tokens rest
      simp [LoopStmt.listSize, LoopStmt.size, LoopStmt.listTokens, LoopStmt.tokens]
      omega
  | .whileLoop op left right body :: rest => by
      have := Expr.size_le_tokens (.binary op left right)
      have := Stmt.listSize_le_tokens body
      have := LoopStmt.listSize_le_tokens rest
      simp [LoopStmt.listSize, LoopStmt.size, LoopStmt.listTokens, LoopStmt.tokens]
      omega

def LoopFile.NamesOk (file : LoopFile) : Prop :=
  (∀ function ∈ file.functions, function.NamesOk) ∧
    isReserved file.contract = false ∧ isReserved file.method.name = false ∧
    (∀ parameter ∈ file.method.parameters, isReserved parameter = false) ∧
    LoopStmt.ListNamesOk file.method.body ∧ file.method.result.NamesOk

theorem parseLoopFileWith_tokens (file : LoopFile) (names : file.NamesOk) (fuel : Nat)
    (functionsFuel : ∀ function ∈ file.functions,
      Stmt.listSize function.body < fuel ∧ function.result.size < fuel)
    (bodyFuel : LoopStmt.listSize file.method.body < fuel)
    (resultFuel : file.method.result.size < fuel) :
    parseLoopFileWith fuel file.tokens = some file := by
  obtain ⟨functionsOk, contractOk, methodOk, parametersOk, bodyOk, resultOk⟩ := names
  have bodyParse := parseLoopStmts_tokens file.method.body fuel
    (.ident "return" :: (file.method.result.tokens ++
      [.symbol ';', .symbol '}', .symbol '}'])) bodyOk bodyFuel rfl
  have resultParse := parseExpr_tokens file.method.result fuel
    [.symbol ';', .symbol '}', .symbol '}'] resultOk resultFuel (by simp)
  have parametersParse := parseParameters_tokens file.method.parameters
    (signatureTokens ++ (LoopStmt.listTokens file.method.body ++ (.ident "return" ::
      (file.method.result.tokens ++ [.symbol ';', .symbol '}', .symbol '}'])))) parametersOk rfl
  have functionsLength := functions_length_le_tokens file.functions
  have functionsParse := parseFunctions_tokens file.functions (file.tokens.length + 1) fuel
    (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
      .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
        (signatureTokens ++ (LoopStmt.listTokens file.method.body ++ (.ident "return" ::
          (file.method.result.tokens ++ [.symbol ';', .symbol '}', .symbol '}']))))))
    (fun function mem => ⟨functionsOk function mem, functionsFuel function mem⟩)
    (by simp only [LoopFile.tokens, List.length_append] at functionsLength ⊢; omega)
    (by simp)
  have aliasesParse := parseAliasImport_tokens file.opcodeAliases
    (file.functions.flatMap FunctionDecl.tokens ++
      (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
        .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
          (signatureTokens ++ (LoopStmt.listTokens file.method.body ++ (.ident "return" ::
            (file.method.result.tokens ++ [.symbol ';', .symbol '}', .symbol '}'])))))))
    (by
      cases functions : file.functions with
      | nil => simp
      | cons function rest => simp [FunctionDecl.tokens])
  unfold parseLoopFileWith
  conv => lhs; arg 1; rw [LoopFile.tokens]
  simp only [List.append_assoc, List.cons_append, List.nil_append, expectTokens_append,
    Option.bind_eq_bind, Option.bind_some]
  rw [aliasesParse]
  simp only [Option.bind_some]
  rw [functionsParse]
  simp [expectTokens, parseName_cons contractOk, parseName_cons methodOk, parametersParse,
    expectTokens_append, bodyParse, resultParse]

/-- **Parser round trip.** Parsing the tokens of a loop file with non-reserved
names returns that file. -/
theorem parseLoopFile_tokens (file : LoopFile) (names : file.NamesOk) :
    parseLoopFile file.tokens = some file := by
  have bodySize := LoopStmt.listSize_le_tokens file.method.body
  have resultSize := Expr.size_le_tokens file.method.result
  apply parseLoopFileWith_tokens file names
  · intro function mem
    have := functions_sizes_le_tokens mem
    simp only [LoopFile.tokens, List.length_append]
    omega
  · simp only [LoopFile.tokens, List.length_append] at bodySize ⊢
    omega
  · simp only [LoopFile.tokens, List.length_append] at resultSize ⊢
    omega

/-! ### Printed pieces -/

def LoopStmt.linePieces (indent : Nat) : LoopStmt → List (List Piece)
  | .plain statement => statement.linePieces indent
  | .whileLoop op left right body =>
      [blanks indent ++ [word "while", space] ++ (Expr.binary op left right).pieces ++
          [space, sym '{']] ++
        Stmt.listLinePieces (indent + 4) body ++ [blanks indent ++ [sym '}']]

def LoopStmt.listLinePieces (indent : Nat) : List LoopStmt → List (List Piece)
  | [] => []
  | statement :: rest => statement.linePieces indent ++ LoopStmt.listLinePieces indent rest

theorem LoopStmt.lines_toList (indent : Nat) : (statement : LoopStmt) →
    (statement.lines indent).map String.toList = (statement.linePieces indent).map render
  | .plain statement => Stmt.lines_toList indent statement
  | .whileLoop op left right body => by
      simp [LoopStmt.lines, LoopStmt.linePieces, indentLine_toList, render_append, render_blanks,
        render, Piece.chars, Token.chars, word, sym, space, Expr.print_toList,
        Stmt.listLines_toList (indent + 4) body]

theorem LoopStmt.listLines_toList (indent : Nat) : (statements : List LoopStmt) →
    (LoopStmt.listLines indent statements).map String.toList =
      (LoopStmt.listLinePieces indent statements).map render
  | [] => rfl
  | statement :: rest => by
      simp [LoopStmt.listLines, LoopStmt.listLinePieces, LoopStmt.lines_toList indent statement,
        LoopStmt.listLines_toList indent rest]

theorem LoopStmt.linePieces_tokens (indent : Nat) : (statement : LoopStmt) →
    ((statement.linePieces indent).map tokensOf).flatten = statement.tokens
  | .plain statement => Stmt.linePieces_tokens indent statement
  | .whileLoop op left right body => by
      simp [LoopStmt.linePieces, LoopStmt.tokens, tokensOf_append, tokensOf_blanks, tokensOf,
        word, sym, space, Expr.tokensOf_pieces, Stmt.listLinePieces_tokens (indent + 4) body]

theorem LoopStmt.listLinePieces_tokens (indent : Nat) : (statements : List LoopStmt) →
    ((LoopStmt.listLinePieces indent statements).map tokensOf).flatten =
      LoopStmt.listTokens statements
  | [] => rfl
  | statement :: rest => by
      simp [LoopStmt.listLinePieces, LoopStmt.listTokens,
        LoopStmt.linePieces_tokens indent statement, LoopStmt.listLinePieces_tokens indent rest]

theorem LoopStmt.linePieces_separated (indent : Nat) : (statement : LoopStmt) →
    (∀ name ∈ statement.identifiers, ValidIdentifier name) →
    ∀ line ∈ statement.linePieces indent, Separated line
  | .plain statement, valid, line, mem => Stmt.linePieces_separated indent statement valid line mem
  | .whileLoop op left right body, valid, line, mem => by
      simp only [LoopStmt.linePieces, List.mem_append, List.mem_singleton] at mem
      rcases mem with (same | mem) | same
      · subst same
        have conditionPart := Expr.separated_append (.binary op left right)
          (fun name mem => valid name (by
            simp only [Expr.identifiers, List.mem_append] at mem
            simp only [LoopStmt.identifiers, List.mem_append]
            rcases mem with mem | mem <;> simp [mem]))
          [space, sym '{'] (Separated.cons_space (sym_valid (by decide))) head_space
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_space conditionPart) head_space)
      · exact Stmt.listLinePieces_separated (indent + 4) body
          (fun name mem => valid name (by simp [LoopStmt.identifiers, mem])) line mem
      · subst same
        exact Separated.blanks_append indent (sym_valid (by decide))

theorem LoopStmt.listLinePieces_separated (indent : Nat) : (statements : List LoopStmt) →
    (∀ name ∈ LoopStmt.listIdentifiers statements, ValidIdentifier name) →
    ∀ line ∈ LoopStmt.listLinePieces indent statements, Separated line
  | [], _, _, mem => by simp [LoopStmt.listLinePieces] at mem
  | statement :: rest, valid, line, mem => by
      simp only [LoopStmt.listLinePieces, List.mem_append] at mem
      rcases mem with mem | mem
      · exact LoopStmt.linePieces_separated indent statement
          (fun name found => valid name (by simp [LoopStmt.listIdentifiers, found])) line mem
      · exact LoopStmt.listLinePieces_separated indent rest
          (fun name found => valid name (by simp [LoopStmt.listIdentifiers, found])) line mem

/-- The pieces of `SourceFile.linePieces` around a loop method body. -/
def LoopFile.linePieces (file : LoopFile) : List (List Piece) :=
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
  LoopStmt.listLinePieces 8 file.method.body ++
  [blanks 8 ++ [word "return", space] ++ file.method.result.pieces ++ [sym ';'],
    blanks 4 ++ [sym '}'], [sym '}']]

theorem LoopFile.lines_toList (file : LoopFile) :
    file.lines.map String.toList = file.linePieces.map render := by
  simp only [LoopFile.lines, LoopFile.linePieces, List.map_append, aliasImportLines_toList,
    functions_lines_toList]
  simp [LoopStmt.listLines_toList, parameterText_toList, Expr.print_toList, render_append,
    render_blanks, render, Piece.chars, Token.chars, word, sym, space]

theorem LoopFile.linePieces_tokens (file : LoopFile) :
    (file.linePieces.map tokensOf).flatten = file.tokens := by
  simp only [LoopFile.linePieces, LoopFile.tokens, List.map_append, List.flatten_append,
    aliasImportLinePieces_tokens, functions_linePieces_tokens]
  simp [importTokens, signatureTokens, LoopStmt.listLinePieces_tokens, parameterPieces_tokens,
    Expr.tokensOf_pieces, tokensOf_append, tokensOf_blanks, tokensOf, word, sym, space]

/-- Every identifier of the loop file is lexically valid. -/
def LoopFile.IdentifiersValid (file : LoopFile) : Prop :=
  (∀ alias ∈ file.opcodeAliases, ValidIdentifier alias.1 ∧ ValidIdentifier alias.2) ∧
    (∀ function ∈ file.functions, ∀ name ∈ function.identifiers, ValidIdentifier name) ∧
    ValidIdentifier file.contract ∧ ValidIdentifier file.method.name ∧
    (∀ parameter ∈ file.method.parameters, ValidIdentifier parameter) ∧
    (∀ name ∈ LoopStmt.listIdentifiers file.method.body, ValidIdentifier name) ∧
    (∀ name ∈ file.method.result.identifiers, ValidIdentifier name)

/-- The loop file without its method body. Its lines are the loop file's lines
other than those of the body. -/
def LoopFile.skeleton (file : LoopFile) : SourceFile where
  opcodeAliases := file.opcodeAliases
  functions := file.functions
  contract := file.contract
  method := {
    name := file.method.name, parameters := file.method.parameters, body := [],
    result := file.method.result }

theorem LoopFile.linePieces_separated (file : LoopFile) (valid : file.IdentifiersValid) :
    ∀ line ∈ file.linePieces, Separated line := by
  obtain ⟨aliasesValid, functionsValid, contractValid, methodValid, parametersValid, bodyValid,
    resultValid⟩ := valid
  have skeleton := file.skeleton.linePieces_separated ⟨aliasesValid, functionsValid,
    contractValid, methodValid, parametersValid,
    by simp [LoopFile.skeleton, Stmt.listIdentifiers], resultValid⟩
  intro line mem
  unfold LoopFile.linePieces at mem
  rw [List.mem_append, List.mem_append] at mem
  rcases mem with (mem | mem) | mem
  · exact skeleton line (List.mem_append_left _ (List.mem_append_left _ mem))
  · exact LoopStmt.listLinePieces_separated 8 file.method.body bodyValid line mem
  · exact skeleton line (List.mem_append_right _ mem)

theorem LoopFile.print_toList (file : LoopFile) :
    file.print.toList = render (joinLines file.linePieces) := by
  rw [LoopFile.print, String.toList_append, String.toList_intercalate, joinLines, render_append,
    render_intercalate, LoopFile.lines_toList]
  rfl

/-- **Text round trip.** The printed text of a loop file with lexically valid,
non-reserved names parses back to that file. -/
theorem parseLoopSource_print (file : LoopFile) (names : file.NamesOk)
    (valid : file.IdentifiersValid) : parseLoopSource file.print = some file := by
  rw [parseLoopSource, LoopFile.print_toList,
    lex_render (joinLines_separated _ (file.linePieces_separated valid)), Option.bind_some,
    tokensOf_joinLines, LoopFile.linePieces_tokens]
  exact parseLoopFile_tokens file names

/-- The loop meaning of a printed loop file's text is the meaning of the
file. -/
theorem loopSourceCall_print (file : LoopFile) (names : file.NamesOk)
    (valid : file.IdentifiersValid) (fuel : Nat) (method : String) (arguments : List Nat) :
    loopSourceCall fuel file.print method arguments = file.call fuel method arguments := by
  simp [loopSourceCall, parseLoopSource_print file names valid]

end Solcore.Synthesis.Source.ScalarMeaning
