import Solcore.Synthesis.Source.ScalarMeaning.KeyedSemantics
import Solcore.Synthesis.Source.ScalarMeaning.RollbackText

/-! Text of keyed programs. `parseKeyedSource` lexes a complete text as
`parseSource` does and parses it with the rollback grammar, extended by sum
`let`s. A sum `let` is recognized from its tokens: its value goes on with `+`
after its first and second expressions, where a loop-free `let` value ends with
`;`, an operation `let` has one operator and the value of a call `let` is no
complete expression. The printed text of every keyed file with valid,
non-reserved names parses back to that file. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

/-! ### Tokens -/

def KeyedStmt.tokens : KeyedStmt → List Token
  | .rollback statement => statement.tokens
  | .letSum identifier type first second third =>
      [.ident "let", .ident identifier, .symbol ':'] ++ type.tokens ++ [.symbol '='] ++
        first.tokens ++ [.symbol '+'] ++ second.tokens ++ [.symbol '+'] ++ third.tokens ++
        [.symbol ';']

def KeyedStmt.listTokens : List KeyedStmt → List Token
  | [] => []
  | statement :: rest => statement.tokens ++ KeyedStmt.listTokens rest

def KeyedFile.tokens (file : KeyedFile) : List Token :=
  importTokens ++ rollbackImportTokens file.opcodeAliases ++
    file.functions.flatMap FunctionDecl.tokens ++
    [.ident "contract", .ident file.contract, .symbol '{', .ident "function",
      .ident file.method.name, .symbol '('] ++ parameterTokens file.method.parameters ++
    signatureTokens ++ KeyedStmt.listTokens file.method.body ++
    [.ident "return", .ident "uint256", .symbol '('] ++ file.method.result.tokens ++
    [.symbol ')', .symbol ';', .symbol '}', .symbol '}']

/-! ### Parser -/

/-- `let x: T = a + b + c;` -/
def parseLetSum (fuel : Nat) (tokens : List Token) : Option (KeyedStmt × List Token) := do
  let rest ← expectTokens [.ident "let"] tokens
  let (identifier, rest) ← parseName rest
  let rest ← expectTokens [.symbol ':'] rest
  let (type, rest) ← parseLocalType rest
  let rest ← expectTokens [.symbol '='] rest
  let (first, rest) ← parseExpr fuel rest
  let rest ← expectTokens [.symbol '+'] rest
  let (second, rest) ← parseExpr fuel rest
  let rest ← expectTokens [.symbol '+'] rest
  let (third, rest) ← parseExpr fuel rest
  let rest ← expectTokens [.symbol ';'] rest
  some (.letSum identifier type first second third, rest)

/-- A sum `let`, or otherwise a rollback statement. -/
def parseKeyedStmt (fuel : Nat) (tokens : List Token) : Option (KeyedStmt × List Token) :=
  match parseLetSum fuel tokens with
  | some parsed => some parsed
  | none => (parseRollbackStmt fuel tokens).map fun parsed => (.rollback parsed.1, parsed.2)

def parseKeyedStmts : Nat → List Token → Option (List KeyedStmt × List Token)
  | 0, _ => none
  | fuel + 1, tokens =>
      if blockEnds tokens then some ([], tokens)
      else do
        let (statement, rest) ← parseKeyedStmt fuel tokens
        let (statements, rest) ← parseKeyedStmts fuel rest
        some (statement :: statements, rest)

/-- `parseRollbackFileWith` with a keyed method body. -/
def parseKeyedFileWith (fuel : Nat) (tokens : List Token) : Option KeyedFile := do
  let rest ← expectTokens importTokens tokens
  let (opcodeAliases, rest) ← parseRollbackImport rest
  let (functions, rest) ← parseFunctions (tokens.length + 1) fuel rest
  let rest ← expectTokens [.ident "contract"] rest
  let (contract, rest) ← parseName rest
  let rest ← expectTokens [.symbol '{', .ident "function"] rest
  let (method, rest) ← parseName rest
  let rest ← expectTokens [.symbol '('] rest
  let (parameters, rest) ← parseParameters rest
  let rest ← expectTokens signatureTokens rest
  let (body, rest) ← parseKeyedStmts fuel rest
  let rest ← expectTokens [.ident "return", .ident "uint256", .symbol '('] rest
  let (result, rest) ← parseOperand fuel rest
  let rest ← expectTokens [.symbol ')', .symbol ';', .symbol '}', .symbol '}'] rest
  if rest = [] then
    some ⟨opcodeAliases, functions, contract, ⟨method, parameters, body, result⟩⟩
  else none

/-- Parse a complete token stream; one more than its length bounds nesting. -/
def parseKeyedFile (tokens : List Token) : Option KeyedFile :=
  parseKeyedFileWith (tokens.length + 1) tokens

def parseKeyedSource (source : String) : Option KeyedFile :=
  (lex source.toList).bind parseKeyedFile

/-- The outcome of calling `method` from `storage` on the contract written in
`source`, read as a keyed program. -/
def keyedSourceCall (source : String) (storage : Storage) (method : String)
    (arguments : List Nat) : Option RollbackOutcome :=
  (parseKeyedSource source).bind fun file => file.call storage method arguments

/-! ### Sizes and names -/

def KeyedStmt.size : KeyedStmt → Nat
  | .rollback statement => statement.size
  | .letSum _ _ first second third => first.size + second.size + third.size

def KeyedStmt.listSize : List KeyedStmt → Nat
  | [] => 0
  | statement :: rest => statement.size + KeyedStmt.listSize rest + 1

def KeyedStmt.NamesOk (statement : KeyedStmt) : Prop :=
  ∀ name ∈ statement.identifiers, isReserved name = false

def KeyedStmt.ListNamesOk (statements : List KeyedStmt) : Prop :=
  ∀ name ∈ KeyedStmt.listIdentifiers statements, isReserved name = false

def KeyedFile.NamesOk (file : KeyedFile) : Prop :=
  (∀ function ∈ file.functions, function.NamesOk) ∧
    isReserved file.contract = false ∧ isReserved file.method.name = false ∧
    (∀ parameter ∈ file.method.parameters, isReserved parameter = false) ∧
    KeyedStmt.ListNamesOk file.method.body ∧ file.method.result.NamesOk

/-! ### Round trip -/

theorem parseLetSum_tokens (identifier : String) (type : LocalType) (first second third : Expr)
    (fuel : Nat) (rest : List Token)
    (names : (KeyedStmt.letSum identifier type first second third).NamesOk)
    (enough : (KeyedStmt.letSum identifier type first second third).size < fuel) :
    parseLetSum fuel ((KeyedStmt.letSum identifier type first second third).tokens ++ rest) =
      some (.letSum identifier type first second third, rest) := by
  have identifierOk : isReserved identifier = false :=
    names identifier (by simp [KeyedStmt.identifiers])
  have firstParse := parseExpr_tokens first fuel
    (.symbol '+' :: (second.tokens ++ .symbol '+' :: (third.tokens ++ .symbol ';' :: rest)))
    (fun name mem => names name (by simp [KeyedStmt.identifiers, mem]))
    (by simp only [KeyedStmt.size] at enough; omega) (by simp)
  have secondParse := parseExpr_tokens second fuel
    (.symbol '+' :: (third.tokens ++ .symbol ';' :: rest))
    (fun name mem => names name (by simp [KeyedStmt.identifiers, mem]))
    (by simp only [KeyedStmt.size] at enough; omega) (by simp)
  have thirdParse := parseExpr_tokens third fuel (.symbol ';' :: rest)
    (fun name mem => names name (by simp [KeyedStmt.identifiers, mem]))
    (by simp only [KeyedStmt.size] at enough; omega) (by simp)
  simp only [KeyedStmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
  simp [parseLetSum, expectTokens, parseName_cons identifierOk, LocalType.parse_tokens,
    firstParse, secondParse, thirdParse]

/-- No rollback statement reads as a sum `let`. -/
theorem parseLetSum_rollback (statement : RollbackStmt) (names : statement.NamesOk)
    (fuel : Nat) (enough : statement.size < fuel) (rest : List Token) :
    parseLetSum fuel (statement.tokens ++ rest) = none := by
  cases statement with
  | storage statement =>
      cases statement with
      | plain statement =>
          cases statement with
          | letDecl identifier type initializer =>
              have identifierOk : isReserved identifier = false :=
                names identifier (by
                  simp [RollbackStmt.identifiers, StorageStmt.identifiers, Stmt.identifiers])
              have initializerParse := parseExpr_tokens initializer fuel (.symbol ';' :: rest)
                (fun name mem => names name (by
                  simp [RollbackStmt.identifiers, StorageStmt.identifiers, Stmt.identifiers, mem]))
                (by simp only [RollbackStmt.size, StorageStmt.size, Stmt.size] at enough; omega)
                (by simp)
              simp only [RollbackStmt.tokens, StorageStmt.tokens, Stmt.tokens, List.append_assoc,
                List.cons_append, List.nil_append]
              simp [parseLetSum, expectTokens, parseName_cons identifierOk,
                LocalType.parse_tokens, initializerParse]
          | assign identifier value =>
              have identifierOk : isReserved identifier = false :=
                names identifier (by
                  simp [RollbackStmt.identifiers, StorageStmt.identifiers, Stmt.identifiers])
              have notLet : "let" ≠ identifier :=
                fun same => (not_reserved_ne identifierOk).1 same.symm
              simp [RollbackStmt.tokens, StorageStmt.tokens, Stmt.tokens, parseLetSum,
                expectTokens, notLet]
          | ifElse =>
              simp [RollbackStmt.tokens, StorageStmt.tokens, Stmt.tokens, parseLetSum,
                expectTokens]
          | matchPair =>
              simp [RollbackStmt.tokens, StorageStmt.tokens, Stmt.tokens, parseLetSum,
                expectTokens]
          | matchSum =>
              simp [RollbackStmt.tokens, StorageStmt.tokens, Stmt.tokens, parseLetSum,
                expectTokens]
      | letCall identifier type callee op left right =>
          have identifierOk : isReserved identifier = false :=
            names identifier (by simp [RollbackStmt.identifiers, StorageStmt.identifiers])
          have calleeOk : isReserved callee = false :=
            names callee (by simp [RollbackStmt.identifiers, StorageStmt.identifiers])
          have rightSize := Expr.size_pos right
          have callParse := parseExpr_call_operation callee calleeOk op left
            (fun name mem => names name (by
              simp [RollbackStmt.identifiers, StorageStmt.identifiers, mem])) fuel
            (by simp only [RollbackStmt.size, StorageStmt.size] at enough; omega)
            (right.tokens ++ .symbol ')' :: .symbol ';' :: rest)
          simp only [RollbackStmt.tokens, StorageStmt.tokens, List.append_assoc, List.cons_append,
            List.nil_append]
          simp [parseLetSum, expectTokens, parseName_cons identifierOk, LocalType.parse_tokens,
            callParse]
      | store => simp [RollbackStmt.tokens, StorageStmt.tokens, parseLetSum, expectTokens]
  | letOperation identifier type op left right =>
      have identifierOk : isReserved identifier = false :=
        names identifier (by simp [RollbackStmt.identifiers])
      have leftParse := parseExpr_tokens left fuel (op.token :: (right.tokens ++ .symbol ';' :: rest))
        (fun name mem => names name (by simp [RollbackStmt.identifiers, mem]))
        (by simp only [RollbackStmt.size] at enough; omega)
        (by simpa using BinaryOp.token_ne_open op)
      have rightParse := parseExpr_tokens right fuel (.symbol ';' :: rest)
        (fun name mem => names name (by simp [RollbackStmt.identifiers, mem]))
        (by simp only [RollbackStmt.size] at enough; omega) (by simp)
      simp only [RollbackStmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
      cases op <;>
        simp only [BinaryOp.token] at leftParse <;>
        simp [parseLetSum, expectTokens, parseName_cons identifierOk, LocalType.parse_tokens,
          leftParse, rightParse, BinaryOp.token]
  | revertIf => simp [RollbackStmt.tokens, parseLetSum, expectTokens]

theorem parseKeyedStmt_tokens (statement : KeyedStmt) (names : statement.NamesOk)
    (fuel : Nat) (enough : statement.size < fuel) (rest : List Token) :
    parseKeyedStmt fuel (statement.tokens ++ rest) = some (statement, rest) := by
  cases statement with
  | rollback statement =>
      have statementNames : statement.NamesOk := names
      have statementEnough : statement.size < fuel := enough
      simp only [KeyedStmt.tokens]
      simp [parseKeyedStmt, parseLetSum_rollback statement statementNames fuel statementEnough,
        parseRollbackStmt_tokens statement statementNames fuel statementEnough rest]
  | letSum identifier type first second third =>
      simp [parseKeyedStmt, parseLetSum_tokens identifier type first second third fuel rest names
        enough]

theorem KeyedStmt.blockEnds_tokens (statement : KeyedStmt) (names : statement.NamesOk)
    (rest : List Token) : blockEnds (statement.tokens ++ rest) = false := by
  cases statement with
  | rollback statement => exact RollbackStmt.blockEnds_tokens statement names rest
  | letSum => rfl

theorem parseKeyedStmts_tokens : ∀ (statements : List KeyedStmt) (fuel : Nat)
    (rest : List Token), KeyedStmt.ListNamesOk statements →
    KeyedStmt.listSize statements < fuel → blockEnds rest = true →
    parseKeyedStmts fuel (KeyedStmt.listTokens statements ++ rest) = some (statements, rest)
  | [], fuel + 1, rest, _, _, ends => by
      simp [KeyedStmt.listTokens, parseKeyedStmts, ends]
  | statement :: more, fuel + 1, rest, names, enough, ends => by
      have statementNames : statement.NamesOk :=
        fun name mem => names name (by simp [KeyedStmt.listIdentifiers, mem])
      have moreNames : KeyedStmt.ListNamesOk more :=
        fun name mem => names name (by simp [KeyedStmt.listIdentifiers, mem])
      have statementParse := parseKeyedStmt_tokens statement statementNames fuel
        (by simp only [KeyedStmt.listSize] at enough; omega)
        (KeyedStmt.listTokens more ++ rest)
      have moreParse := parseKeyedStmts_tokens more fuel rest moreNames
        (by simp only [KeyedStmt.listSize] at enough; omega) ends
      simp only [KeyedStmt.listTokens, List.append_assoc]
      simp [parseKeyedStmts, KeyedStmt.blockEnds_tokens statement statementNames,
        statementParse, moreParse]

theorem KeyedStmt.size_lt_tokens (statement : KeyedStmt) :
    statement.size < statement.tokens.length := by
  cases statement with
  | rollback statement => exact RollbackStmt.size_lt_tokens statement
  | letSum identifier type first second third =>
      have := Expr.size_le_tokens first
      have := Expr.size_le_tokens second
      have := Expr.size_le_tokens third
      simp only [KeyedStmt.size, KeyedStmt.tokens, List.length_append, List.length_cons,
        List.length_nil]
      omega

theorem KeyedStmt.listSize_le_tokens : (statements : List KeyedStmt) →
    KeyedStmt.listSize statements ≤ (KeyedStmt.listTokens statements).length
  | [] => by simp [KeyedStmt.listSize, KeyedStmt.listTokens]
  | statement :: rest => by
      have := KeyedStmt.size_lt_tokens statement
      have := KeyedStmt.listSize_le_tokens rest
      simp only [KeyedStmt.listSize, KeyedStmt.listTokens, List.length_append]
      omega

theorem parseKeyedFileWith_tokens (file : KeyedFile) (names : file.NamesOk) (fuel : Nat)
    (functionsFuel : ∀ function ∈ file.functions,
      Stmt.listSize function.body < fuel ∧ function.result.size < fuel)
    (bodyFuel : KeyedStmt.listSize file.method.body < fuel)
    (resultFuel : file.method.result.size < fuel) :
    parseKeyedFileWith fuel file.tokens = some file := by
  obtain ⟨functionsOk, contractOk, methodOk, parametersOk, bodyOk, resultOk⟩ := names
  have resultParse := parseOperand_tokens file.method.result fuel (.symbol ')')
    [.symbol ';', .symbol '}', .symbol '}'] resultOk resultFuel (Or.inl rfl)
  have bodyParse := parseKeyedStmts_tokens file.method.body fuel
    (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
      [.symbol ')', .symbol ';', .symbol '}', .symbol '}'])) bodyOk bodyFuel rfl
  have parametersParse := parseParameters_tokens file.method.parameters
    (signatureTokens ++ (KeyedStmt.listTokens file.method.body ++
      (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
        [.symbol ')', .symbol ';', .symbol '}', .symbol '}'])))) parametersOk rfl
  have functionsLength := functions_length_le_tokens file.functions
  have functionsParse := parseFunctions_tokens file.functions (file.tokens.length + 1) fuel
    (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
      .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
        (signatureTokens ++ (KeyedStmt.listTokens file.method.body ++
          (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
            [.symbol ')', .symbol ';', .symbol '}', .symbol '}']))))))
    (fun function mem => ⟨functionsOk function mem, functionsFuel function mem⟩)
    (by simp only [KeyedFile.tokens, List.length_append] at functionsLength ⊢; omega)
    (by simp)
  have importParse := parseRollbackImport_tokens file.opcodeAliases
    (file.functions.flatMap FunctionDecl.tokens ++
      (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
        .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
          (signatureTokens ++ (KeyedStmt.listTokens file.method.body ++
            (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
              [.symbol ')', .symbol ';', .symbol '}', .symbol '}'])))))))
  unfold parseKeyedFileWith
  conv => lhs; arg 1; rw [KeyedFile.tokens]
  simp only [List.append_assoc, List.cons_append, List.nil_append, expectTokens_append,
    Option.bind_eq_bind, Option.bind_some]
  rw [importParse]
  simp only [Option.bind_some]
  rw [functionsParse]
  simp [expectTokens, parseName_cons contractOk, parseName_cons methodOk, parametersParse,
    expectTokens_append, bodyParse, resultParse]

/-- **Parser round trip.** Parsing the tokens of a keyed file with non-reserved
names returns that file. -/
theorem parseKeyedFile_tokens (file : KeyedFile) (names : file.NamesOk) :
    parseKeyedFile file.tokens = some file := by
  have bodySize := KeyedStmt.listSize_le_tokens file.method.body
  have resultSize := Operand.size_le_tokens file.method.result
  apply parseKeyedFileWith_tokens file names
  · intro function mem
    have := functions_sizes_le_tokens mem
    simp only [KeyedFile.tokens, List.length_append]
    omega
  · simp only [KeyedFile.tokens, List.length_append] at bodySize ⊢
    omega
  · simp only [KeyedFile.tokens, List.length_append, List.length_cons] at resultSize ⊢
    omega

/-! ### Printed pieces -/

def KeyedStmt.linePieces (indent : Nat) : KeyedStmt → List (List Piece)
  | .rollback statement => statement.linePieces indent
  | .letSum identifier type first second third =>
      [blanks indent ++ [word "let", space, word identifier, sym ':', space] ++ type.pieces ++
        [space, sym '=', space] ++ first.pieces ++ [space, sym '+', space] ++ second.pieces ++
        [space, sym '+', space] ++ third.pieces ++ [sym ';']]

def KeyedStmt.listLinePieces (indent : Nat) : List KeyedStmt → List (List Piece)
  | [] => []
  | statement :: rest => statement.linePieces indent ++ KeyedStmt.listLinePieces indent rest

theorem KeyedStmt.lines_toList (indent : Nat) : (statement : KeyedStmt) →
    (statement.lines indent).map String.toList = (statement.linePieces indent).map render
  | .rollback statement => RollbackStmt.lines_toList indent statement
  | .letSum identifier type first second third => by
      simp [KeyedStmt.lines, KeyedStmt.linePieces, indentLine_toList, render_append,
        render_blanks, render, Piece.chars, Token.chars, word, sym, space,
        LocalType.spelling_toList, Expr.print_toList]

theorem KeyedStmt.listLines_toList (indent : Nat) : (statements : List KeyedStmt) →
    (KeyedStmt.listLines indent statements).map String.toList =
      (KeyedStmt.listLinePieces indent statements).map render
  | [] => rfl
  | statement :: rest => by
      simp [KeyedStmt.listLines, KeyedStmt.listLinePieces, KeyedStmt.lines_toList indent statement,
        KeyedStmt.listLines_toList indent rest]

theorem KeyedStmt.linePieces_tokens (indent : Nat) : (statement : KeyedStmt) →
    ((statement.linePieces indent).map tokensOf).flatten = statement.tokens
  | .rollback statement => RollbackStmt.linePieces_tokens indent statement
  | .letSum identifier type first second third => by
      simp [KeyedStmt.linePieces, KeyedStmt.tokens, tokensOf_append, tokensOf_blanks, tokensOf,
        word, sym, space, LocalType.tokensOf_pieces, Expr.tokensOf_pieces]

theorem KeyedStmt.listLinePieces_tokens (indent : Nat) : (statements : List KeyedStmt) →
    ((KeyedStmt.listLinePieces indent statements).map tokensOf).flatten =
      KeyedStmt.listTokens statements
  | [] => rfl
  | statement :: rest => by
      simp [KeyedStmt.listLinePieces, KeyedStmt.listTokens,
        KeyedStmt.linePieces_tokens indent statement, KeyedStmt.listLinePieces_tokens indent rest]

theorem KeyedStmt.linePieces_separated (indent : Nat) : (statement : KeyedStmt) →
    (∀ name ∈ statement.identifiers, ValidIdentifier name) →
    ∀ line ∈ statement.linePieces indent, Separated line
  | .rollback statement, valid, line, mem =>
      RollbackStmt.linePieces_separated indent statement valid line mem
  | .letSum identifier type first second third, valid, line, mem => by
      simp only [KeyedStmt.linePieces, List.mem_singleton] at mem
      subst mem
      have within : ∀ name, name ∈ first.identifiers ∨ name ∈ second.identifiers ∨
          name ∈ third.identifiers → ValidIdentifier name := by
        intro name found
        apply valid name
        simp only [KeyedStmt.identifiers, List.mem_cons, List.mem_append]
        rcases found with found | found | found <;> simp [found]
      have thirdPart := Expr.separated_append third
        (fun name found => within name (Or.inr (Or.inr found))) [sym ';']
        (sym_valid (by decide)) (head_sym (by decide))
      have secondPart := Expr.separated_append second
        (fun name found => within name (Or.inr (Or.inl found)))
        (space :: sym '+' :: space :: (third.pieces ++ [sym ';']))
        (Separated.cons_space (Separated.cons_sym (by decide) (Separated.cons_space thirdPart)))
        head_space
      have firstPart := Expr.separated_append first
        (fun name found => within name (Or.inl found))
        (space :: sym '+' :: space :: (second.pieces ++ space :: sym '+' :: space ::
          (third.pieces ++ [sym ';'])))
        (Separated.cons_space (Separated.cons_sym (by decide) (Separated.cons_space secondPart)))
        head_space
      have typePart := LocalType.separated_append type _ (Separated.cons_space
        (Separated.cons_equal (Separated.cons_space firstPart) (fun next same => by
          cases same; rfl))) head_space
      simp only [List.append_assoc, List.cons_append, List.nil_append] at typePart ⊢
      exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
        (Separated.cons_space (Separated.cons_word
          (valid identifier (by simp [KeyedStmt.identifiers]))
          (Separated.cons_sym (by decide) (Separated.cons_space typePart))
          (head_sym (by decide))))
        head_space)

theorem KeyedStmt.listLinePieces_separated (indent : Nat) :
    (statements : List KeyedStmt) →
    (∀ name ∈ KeyedStmt.listIdentifiers statements, ValidIdentifier name) →
    ∀ line ∈ KeyedStmt.listLinePieces indent statements, Separated line
  | [], _, _, mem => by simp [KeyedStmt.listLinePieces] at mem
  | statement :: rest, valid, line, mem => by
      simp only [KeyedStmt.listLinePieces, List.mem_append] at mem
      rcases mem with mem | mem
      · exact KeyedStmt.linePieces_separated indent statement
          (fun name found => valid name (by simp [KeyedStmt.listIdentifiers, found])) line mem
      · exact KeyedStmt.listLinePieces_separated indent rest
          (fun name found => valid name (by simp [KeyedStmt.listIdentifiers, found])) line mem

def KeyedFile.linePieces (file : KeyedFile) : List (List Piece) :=
  [[word "import", space, sym '*', space, word "from", space, word "std", sym ';'],
    [word "import", space, sym '*', space, word "from", space, word "std", sym '.',
      word "dispatch", sym ';']] ++
  [rollbackImportPieces file.opcodeAliases] ++ [[]] ++
  file.functions.flatMap FunctionDecl.linePieces ++
  [[word "contract", space, word file.contract, space, sym '{'],
    blanks 4 ++ [word "function", space, word file.method.name, sym '('] ++
      parameterPieces file.method.parameters ++
      [sym ')', space, word "public", space, word "returns", space, sym '(', word "uint256",
        sym ')', space, sym '{']] ++
  KeyedStmt.listLinePieces 8 file.method.body ++
  [blanks 8 ++ [word "return", space, word "uint256", sym '('] ++ file.method.result.pieces ++
      [sym ')', sym ';'],
    blanks 4 ++ [sym '}'], [sym '}']]

theorem KeyedFile.lines_toList (file : KeyedFile) :
    file.lines.map String.toList = file.linePieces.map render := by
  simp only [KeyedFile.lines, KeyedFile.linePieces, List.map_append, functions_lines_toList]
  simp [KeyedStmt.listLines_toList, parameterText_toList, Operand.print_toList,
    rollbackImportLine_toList, render_append, render_blanks, render, Piece.chars, Token.chars,
    word, sym, space]

theorem KeyedFile.linePieces_tokens (file : KeyedFile) :
    (file.linePieces.map tokensOf).flatten = file.tokens := by
  simp only [KeyedFile.linePieces, KeyedFile.tokens, List.map_append, List.flatten_append,
    functions_linePieces_tokens]
  simp [importTokens, signatureTokens, KeyedStmt.listLinePieces_tokens,
    parameterPieces_tokens, Operand.tokensOf_pieces, rollbackImportPieces_tokens,
    tokensOf_append, tokensOf_blanks, tokensOf, word, sym, space]

/-- Every identifier of the keyed file is lexically valid. -/
def KeyedFile.IdentifiersValid (file : KeyedFile) : Prop :=
  (∀ alias ∈ file.opcodeAliases, ValidIdentifier alias.1 ∧ ValidIdentifier alias.2) ∧
    (∀ function ∈ file.functions, ∀ name ∈ function.identifiers, ValidIdentifier name) ∧
    ValidIdentifier file.contract ∧ ValidIdentifier file.method.name ∧
    (∀ parameter ∈ file.method.parameters, ValidIdentifier parameter) ∧
    (∀ name ∈ KeyedStmt.listIdentifiers file.method.body, ValidIdentifier name) ∧
    (∀ name ∈ file.method.result.identifiers, ValidIdentifier name)

/-- The keyed file without aliases, method body or returned operand. Its lines
are the keyed file's import, function, contract and closing lines. -/
def KeyedFile.skeleton (file : KeyedFile) : SourceFile where
  opcodeAliases := []
  functions := file.functions
  contract := file.contract
  method := {
    name := file.method.name, parameters := file.method.parameters, body := [],
    result := .number 0 }

theorem KeyedFile.linePieces_separated (file : KeyedFile)
    (valid : file.IdentifiersValid) : ∀ line ∈ file.linePieces, Separated line := by
  obtain ⟨aliasesValid, functionsValid, contractValid, methodValid, parametersValid, bodyValid,
    resultValid⟩ := valid
  have skeleton := file.skeleton.linePieces_separated ⟨by simp [KeyedFile.skeleton],
    functionsValid, contractValid, methodValid, parametersValid,
    by simp [KeyedFile.skeleton, Stmt.listIdentifiers],
    by simp [KeyedFile.skeleton, Expr.identifiers]⟩
  intro line mem
  unfold KeyedFile.linePieces at mem
  rw [List.mem_append] at mem
  rcases mem with mem | mem
  · rw [List.mem_append] at mem
    rcases mem with mem | mem
    · rw [List.mem_append] at mem
      rcases mem with mem | mem
      · rw [List.mem_append] at mem
        rcases mem with mem | mem
        · rw [List.mem_append] at mem
          rcases mem with mem | mem
          · rw [List.mem_append] at mem
            rcases mem with mem | mem
            · exact skeleton line (List.mem_append_left _ (List.mem_append_left _
                (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
                  (List.mem_append_left _ mem))))))
            · simp only [List.mem_singleton] at mem
              subst mem
              exact rollbackImportPieces_separated _ aliasesValid
          · simp only [List.mem_singleton] at mem
            subst mem
            trivial
        · exact skeleton line (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_right _ mem))))
      · exact skeleton line (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ mem)))
    · exact KeyedStmt.listLinePieces_separated 8 file.method.body bodyValid line mem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with same | same | same
    · subst same
      have resultPart := Operand.separated_append file.method.result resultValid
        [sym ')', sym ';'] (Separated.cons_sym (by decide) (sym_valid (by decide)))
        (head_sym (by decide))
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact Separated.blanks_append 8 (Separated.cons_word (keyword_valid (by decide))
        (Separated.cons_space (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_sym (by decide) resultPart) (head_sym (by decide)))) head_space)
    · exact skeleton line (List.mem_append_right _ (by simp [same]))
    · exact skeleton line (List.mem_append_right _ (by simp [same]))

theorem KeyedFile.print_toList (file : KeyedFile) :
    file.print.toList = render (joinLines file.linePieces) := by
  rw [KeyedFile.print, String.toList_append, String.toList_intercalate, joinLines,
    render_append, render_intercalate, KeyedFile.lines_toList]
  rfl

/-- **Text round trip.** The printed text of a keyed file with lexically valid,
non-reserved names parses back to that file. -/
theorem parseKeyedSource_print (file : KeyedFile) (names : file.NamesOk)
    (valid : file.IdentifiersValid) : parseKeyedSource file.print = some file := by
  rw [parseKeyedSource, KeyedFile.print_toList,
    lex_render (joinLines_separated _ (file.linePieces_separated valid)), Option.bind_some,
    tokensOf_joinLines, KeyedFile.linePieces_tokens]
  exact parseKeyedFile_tokens file names

/-- The meaning of a printed keyed file's text is the meaning of the file. -/
theorem keyedSourceCall_print (file : KeyedFile) (names : file.NamesOk)
    (valid : file.IdentifiersValid) (storage : Storage) (method : String)
    (arguments : List Nat) :
    keyedSourceCall file.print storage method arguments = file.call storage method arguments := by
  simp [keyedSourceCall, parseKeyedSource_print file names valid]

end Solcore.Synthesis.Source.ScalarMeaning
