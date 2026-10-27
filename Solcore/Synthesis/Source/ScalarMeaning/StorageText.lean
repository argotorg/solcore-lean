import Solcore.Synthesis.Source.ScalarMeaning.StorageSemantics
import Solcore.Synthesis.Source.ScalarMeaning.Text

/-! Text of storage programs. `parseStorageSource` lexes a complete text as
`parseSource` does and parses it with the same grammar, extended by the storage
import line, `sstore` statements, `let` statements whose value is a call with
one infix operation as its argument, and an infix operation in the returned
`uint256(...)`. Each extension is recognized from its first tokens: a store
starts with `sstore (`, which no loop-free statement starts with, and a call
`let` goes on with an infix operator where the argument of a loop-free call
ends with `)` or `,`. The printed text of every storage file with valid,
non-reserved names parses back to that file. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

/-! ### Tokens -/

def Operand.tokens : Operand → List Token
  | .plain expression => expression.tokens
  | .operation op left right => left.tokens ++ [op.token] ++ right.tokens

def StorageStmt.tokens : StorageStmt → List Token
  | .plain statement => statement.tokens
  | .letCall identifier type callee op left right =>
      [.ident "let", .ident identifier, .symbol ':'] ++ type.tokens ++
        [.symbol '=', .ident callee, .symbol '('] ++ left.tokens ++ [op.token] ++
        right.tokens ++ [.symbol ')', .symbol ';']
  | .store slot value =>
      [.ident "sstore", .symbol '('] ++ slot.tokens ++ [.symbol ','] ++ value.tokens ++
        [.symbol ')', .symbol ';']

def StorageStmt.listTokens : List StorageStmt → List Token
  | [] => []
  | statement :: rest => statement.tokens ++ StorageStmt.listTokens rest

/-- The aliases after `sload, sstore`, after one more comma. -/
def storageAliasTokens : List (String × String) → List Token
  | [] => []
  | alias :: rest => .symbol ',' :: aliasTokens (alias :: rest)

def storageImportTokens (aliases : List (String × String)) : List Token :=
  [.ident "import", .symbol '{', .ident "sload", .symbol ',', .ident "sstore"] ++
    storageAliasTokens aliases ++
    [.symbol '}', .ident "from", .ident "std", .symbol '.', .ident "opcodes", .symbol ';']

def StorageFile.tokens (file : StorageFile) : List Token :=
  importTokens ++ storageImportTokens file.opcodeAliases ++
    file.functions.flatMap FunctionDecl.tokens ++
    [.ident "contract", .ident file.contract, .symbol '{', .ident "function",
      .ident file.method.name, .symbol '('] ++ parameterTokens file.method.parameters ++
    signatureTokens ++ StorageStmt.listTokens file.method.body ++
    [.ident "return", .ident "uint256", .symbol '('] ++ file.method.result.tokens ++
    [.symbol ')', .symbol ';', .symbol '}', .symbol '}']

/-! ### Parser -/

/-- An operand before `,` or `)`: an expression, and when an infix operator
follows it, the operator and its right operand. -/
def parseOperand (fuel : Nat) (tokens : List Token) : Option (Operand × List Token) := do
  let (left, rest) ← parseExpr fuel tokens
  match rest with
  | next :: after =>
      match parseBinaryOp? next with
      | some op => do
          let (right, rest) ← parseExpr fuel after
          some (.operation op left right, rest)
      | none => some (.plain left, rest)
  | [] => some (.plain left, [])

/-- `let x: T = f(a op b);`: a `let` whose value is a call whose argument goes
on with an infix operator. -/
def parseLetCall (fuel : Nat) (tokens : List Token) : Option (StorageStmt × List Token) := do
  let rest ← expectTokens [.ident "let"] tokens
  let (identifier, rest) ← parseName rest
  let rest ← expectTokens [.symbol ':'] rest
  let (type, rest) ← parseLocalType rest
  let rest ← expectTokens [.symbol '='] rest
  let (callee, rest) ← parseName rest
  let rest ← expectTokens [.symbol '('] rest
  let (left, rest) ← parseExpr fuel rest
  match rest with
  | next :: rest => do
      let op ← parseBinaryOp? next
      let (right, rest) ← parseExpr fuel rest
      let rest ← expectTokens [.symbol ')', .symbol ';'] rest
      some (.letCall identifier type callee op left right, rest)
  | [] => none

/-- A store, a call `let`, or otherwise a loop-free statement. -/
def parseStorageStmt (fuel : Nat) (tokens : List Token) : Option (StorageStmt × List Token) :=
  if tokens.take 2 = [.ident "sstore", .symbol '('] then do
    let (slot, rest) ← parseOperand fuel (tokens.drop 2)
    let rest ← expectTokens [.symbol ','] rest
    let (value, rest) ← parseOperand fuel rest
    let rest ← expectTokens [.symbol ')', .symbol ';'] rest
    some (.store slot value, rest)
  else
    match parseLetCall fuel tokens with
    | some parsed => some parsed
    | none => (parseStmt fuel tokens).map fun parsed => (.plain parsed.1, parsed.2)

def parseStorageStmts : Nat → List Token → Option (List StorageStmt × List Token)
  | 0, _ => none
  | fuel + 1, tokens =>
      if blockEnds tokens then some ([], tokens)
      else do
        let (statement, rest) ← parseStorageStmt fuel tokens
        let (statements, rest) ← parseStorageStmts fuel rest
        some (statement :: statements, rest)

/-- `import {sload, sstore, opcode as alias, ...} from std.opcodes;` -/
def parseStorageImport (tokens : List Token) :
    Option (List (String × String) × List Token) := do
  let rest ← expectTokens
    [.ident "import", .symbol '{', .ident "sload", .symbol ',', .ident "sstore"] tokens
  let (aliases, rest) ←
    if rest.head? = some (.symbol ',') then parseAliasList rest.length rest.tail
    else some ([], rest)
  let rest ← expectTokens
    [.symbol '}', .ident "from", .ident "std", .symbol '.', .ident "opcodes", .symbol ';'] rest
  some (aliases, rest)

/-- `parseFileWith` with the storage import line, a storage method body and a
returned operand. -/
def parseStorageFileWith (fuel : Nat) (tokens : List Token) : Option StorageFile := do
  let rest ← expectTokens importTokens tokens
  let (opcodeAliases, rest) ← parseStorageImport rest
  let (functions, rest) ← parseFunctions (tokens.length + 1) fuel rest
  let rest ← expectTokens [.ident "contract"] rest
  let (contract, rest) ← parseName rest
  let rest ← expectTokens [.symbol '{', .ident "function"] rest
  let (method, rest) ← parseName rest
  let rest ← expectTokens [.symbol '('] rest
  let (parameters, rest) ← parseParameters rest
  let rest ← expectTokens signatureTokens rest
  let (body, rest) ← parseStorageStmts fuel rest
  let rest ← expectTokens [.ident "return", .ident "uint256", .symbol '('] rest
  let (result, rest) ← parseOperand fuel rest
  let rest ← expectTokens [.symbol ')', .symbol ';', .symbol '}', .symbol '}'] rest
  if rest = [] then
    some ⟨opcodeAliases, functions, contract, ⟨method, parameters, body, result⟩⟩
  else none

/-- Parse a complete token stream; one more than its length bounds nesting. -/
def parseStorageFile (tokens : List Token) : Option StorageFile :=
  parseStorageFileWith (tokens.length + 1) tokens

def parseStorageSource (source : String) : Option StorageFile :=
  (lex source.toList).bind parseStorageFile

/-- The returned ABI word and the final storage of calling `method` from
`storage` on the contract written in `source`, read as a storage program. -/
def storageSourceCall (source : String) (storage : Storage) (method : String)
    (arguments : List Nat) : Option (Nat × Storage) :=
  (parseStorageSource source).bind fun file => file.call storage method arguments

/-! ### Sizes and names -/

def Operand.size : Operand → Nat
  | .plain expression => expression.size
  | .operation _ left right => left.size + right.size

def StorageStmt.size : StorageStmt → Nat
  | .plain statement => statement.size
  | .letCall _ _ _ _ left right => left.size + right.size
  | .store slot value => slot.size + value.size

def StorageStmt.listSize : List StorageStmt → Nat
  | [] => 0
  | statement :: rest => statement.size + StorageStmt.listSize rest + 1

def Operand.NamesOk (operand : Operand) : Prop :=
  ∀ name ∈ operand.identifiers, isReserved name = false

def StorageStmt.NamesOk (statement : StorageStmt) : Prop :=
  ∀ name ∈ statement.identifiers, isReserved name = false

def StorageStmt.ListNamesOk (statements : List StorageStmt) : Prop :=
  ∀ name ∈ StorageStmt.listIdentifiers statements, isReserved name = false

def StorageFile.NamesOk (file : StorageFile) : Prop :=
  (∀ function ∈ file.functions, function.NamesOk) ∧
    isReserved file.contract = false ∧ isReserved file.method.name = false ∧
    (∀ parameter ∈ file.method.parameters, isReserved parameter = false) ∧
    StorageStmt.ListNamesOk file.method.body ∧ file.method.result.NamesOk

/-! ### Round trip -/

theorem parseBinaryOp?_close : parseBinaryOp? (.symbol ')') = none := by decide

theorem parseBinaryOp?_comma : parseBinaryOp? (.symbol ',') = none := by decide

/-- An operand followed by `)` or `,` parses back. -/
theorem parseOperand_tokens (operand : Operand) (fuel : Nat) (close : Token)
    (more : List Token) (names : operand.NamesOk) (enough : operand.size < fuel)
    (closing : close = .symbol ')' ∨ close = .symbol ',') :
    parseOperand fuel (operand.tokens ++ close :: more) = some (operand, close :: more) := by
  have notOpen : (close :: more).head? ≠ some (.symbol '(') := by
    rcases closing with rfl | rfl <;> simp
  have notOp : parseBinaryOp? close = none := by
    rcases closing with rfl | rfl
    · exact parseBinaryOp?_close
    · exact parseBinaryOp?_comma
  cases operand with
  | plain expression =>
      have parsed := parseExpr_tokens expression fuel (close :: more) names
        (by simpa [Operand.size] using enough) notOpen
      simp [parseOperand, Operand.tokens, parsed, notOp]
  | operation op left right =>
      have leftParse := parseExpr_tokens left fuel (op.token :: (right.tokens ++ close :: more))
        (fun name mem => names name (by simp [Operand.identifiers, mem]))
        (by simp only [Operand.size] at enough; omega)
        (by simpa using BinaryOp.token_ne_open op)
      have rightParse := parseExpr_tokens right fuel (close :: more)
        (fun name mem => names name (by simp [Operand.identifiers, mem]))
        (by simp only [Operand.size] at enough; omega) notOpen
      simp only [Operand.tokens, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseOperand, leftParse, BinaryOp.parse_token, rightParse]

theorem parseLetCall_tokens (identifier : String) (type : LocalType) (callee : String)
    (op : BinaryOp) (left right : Expr) (fuel : Nat) (rest : List Token)
    (names : (StorageStmt.letCall identifier type callee op left right).NamesOk)
    (enough : (StorageStmt.letCall identifier type callee op left right).size < fuel) :
    parseLetCall fuel ((StorageStmt.letCall identifier type callee op left right).tokens ++
      rest) = some (.letCall identifier type callee op left right, rest) := by
  have identifierOk : isReserved identifier = false :=
    names identifier (by simp [StorageStmt.identifiers])
  have calleeOk : isReserved callee = false :=
    names callee (by simp [StorageStmt.identifiers])
  have leftParse := parseExpr_tokens left fuel
    (op.token :: (right.tokens ++ .symbol ')' :: .symbol ';' :: rest))
    (fun name mem => names name (by simp [StorageStmt.identifiers, mem]))
    (by simp only [StorageStmt.size] at enough; omega)
    (by simpa using BinaryOp.token_ne_open op)
  have rightParse := parseExpr_tokens right fuel (.symbol ')' :: .symbol ';' :: rest)
    (fun name mem => names name (by simp [StorageStmt.identifiers, mem]))
    (by simp only [StorageStmt.size] at enough; omega) (by simp)
  simp only [StorageStmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
  simp [parseLetCall, expectTokens, parseName_cons identifierOk, parseName_cons calleeOk,
    LocalType.parse_tokens, leftParse, BinaryOp.parse_token, rightParse]

/-- No loop-free statement reads as a call `let`: after a loop-free call's
first argument comes `)` or `,`, never an infix operator. -/
theorem parseLetCall_plain (statement : Stmt) (names : statement.NamesOk) (fuel : Nat)
    (enough : statement.size < fuel) (rest : List Token) :
    parseLetCall fuel (statement.tokens ++ rest) = none := by
  cases statement with
  | letDecl identifier type initializer =>
      have identifierOk : isReserved identifier = false :=
        names identifier (by simp [Stmt.identifiers])
      have initializerNames : initializer.NamesOk :=
        fun name mem => names name (by simp [Stmt.identifiers, mem])
      have initializerEnough : initializer.size + 1 < fuel := by
        simpa [Stmt.size] using enough
      have prefixParse : ∀ more : List Token,
          parseLetCall fuel ((Stmt.letDecl identifier type initializer).tokens ++ more) =
            (do
              let (callee, after) ← parseName (initializer.tokens ++ .symbol ';' :: more)
              let after ← expectTokens [.symbol '('] after
              let (left, after) ← parseExpr fuel after
              match after with
              | next :: after => do
                  let op ← parseBinaryOp? next
                  let (right, after) ← parseExpr fuel after
                  let after ← expectTokens [.symbol ')', .symbol ';'] after
                  some (StorageStmt.letCall identifier type callee op left right, after)
              | [] => none) := by
        intro more
        simp only [Stmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
        simp [parseLetCall, expectTokens, parseName_cons identifierOk, LocalType.parse_tokens]
      rw [prefixParse]
      cases initializer with
      | name text => simp [Expr.tokens, parseName, expectTokens]
      | number value => simp [Expr.tokens, parseName]
      | bool value => cases value <;> simp [Expr.tokens, parseName, isReserved, reservedWords]
      | unary op operand => simp [Expr.tokens, parseName]
      | binary op left right => simp [Expr.tokens, parseName]
      | typedefRep operand => simp [Expr.tokens, parseName, isReserved, reservedWords]
      | uint256 operand => simp [Expr.tokens, parseName, isReserved, reservedWords]
      | call1 callee first =>
          have calleeOk : isReserved callee = false :=
            initializerNames callee (by simp [Expr.identifiers])
          have firstParse := parseExpr_tokens first fuel (.symbol ')' :: .symbol ';' :: rest)
            (fun name mem => initializerNames name (by simp [Expr.identifiers, mem]))
            (by simp only [Expr.size] at initializerEnough; omega) (by simp)
          simp only [Expr.tokens, List.append_assoc, List.cons_append, List.nil_append]
          simp [parseName_cons calleeOk, expectTokens, firstParse, parseBinaryOp?_close]
      | call2 callee first second =>
          have calleeOk : isReserved callee = false :=
            initializerNames callee (by simp [Expr.identifiers])
          have firstParse := parseExpr_tokens first fuel
            (.symbol ',' :: (second.tokens ++ .symbol ')' :: .symbol ';' :: rest))
            (fun name mem => initializerNames name (by simp [Expr.identifiers, mem]))
            (by simp only [Expr.size] at initializerEnough; omega) (by simp)
          simp only [Expr.tokens, List.append_assoc, List.cons_append, List.nil_append]
          simp [parseName_cons calleeOk, expectTokens, firstParse, parseBinaryOp?_comma]
      | call3 callee first second third =>
          have calleeOk : isReserved callee = false :=
            initializerNames callee (by simp [Expr.identifiers])
          have firstParse := parseExpr_tokens first fuel
            (.symbol ',' :: (second.tokens ++ .symbol ',' :: (third.tokens ++
              .symbol ')' :: .symbol ';' :: rest)))
            (fun name mem => initializerNames name (by simp [Expr.identifiers, mem]))
            (by simp only [Expr.size] at initializerEnough; omega) (by simp)
          simp only [Expr.tokens, List.append_assoc, List.cons_append, List.nil_append]
          simp [parseName_cons calleeOk, expectTokens, firstParse, parseBinaryOp?_comma]
      | tuple first second => simp [Expr.tokens, parseName]
      | inl payload => simp [Expr.tokens, parseName, isReserved, reservedWords]
      | inr payload => simp [Expr.tokens, parseName, isReserved, reservedWords]
  | assign identifier value =>
      have identifierOk : isReserved identifier = false :=
        names identifier (by simp [Stmt.identifiers])
      have notLet : "let" ≠ identifier := fun same => (not_reserved_ne identifierOk).1 same.symm
      simp [Stmt.tokens, parseLetCall, expectTokens, notLet]
  | ifElse condition thenBlock elseBlock => simp [Stmt.tokens, parseLetCall, expectTokens]
  | matchPair scrutinee first second body => simp [Stmt.tokens, parseLetCall, expectTokens]
  | matchSum scrutinee left leftBody right rightBody =>
      simp [Stmt.tokens, parseLetCall, expectTokens]

/-- No loop-free statement starts with `sstore (`. -/
theorem Stmt.take_ne_store (statement : Stmt) (rest : List Token) :
    (statement.tokens ++ rest).take 2 ≠ [.ident "sstore", .symbol '('] := by
  cases statement <;> simp [Stmt.tokens]

theorem parseStorageStmt_tokens (statement : StorageStmt) (names : statement.NamesOk)
    (fuel : Nat) (enough : statement.size < fuel) (rest : List Token) :
    parseStorageStmt fuel (statement.tokens ++ rest) = some (statement, rest) := by
  cases statement with
  | plain statement =>
      have statementNames : statement.NamesOk := names
      have statementEnough : statement.size < fuel := enough
      have statementParse := (parseStmt_tokens_all fuel).1 statement rest statementNames
        statementEnough
      have notStore := Stmt.take_ne_store statement rest
      simp only [StorageStmt.tokens]
      simp [parseStorageStmt, notStore, parseLetCall_plain statement statementNames fuel
        statementEnough rest, statementParse]
  | letCall identifier type callee op left right =>
      have parsed := parseLetCall_tokens identifier type callee op left right fuel rest names
        enough
      simp only [StorageStmt.tokens] at parsed ⊢
      simp only [List.append_assoc, List.cons_append, List.nil_append] at parsed ⊢
      simp [parseStorageStmt, parsed]
  | store slot value =>
      have slotParse := parseOperand_tokens slot fuel (.symbol ',')
        (value.tokens ++ .symbol ')' :: .symbol ';' :: rest)
        (fun name mem => names name (by simp [StorageStmt.identifiers, mem]))
        (by simp only [StorageStmt.size] at enough; omega) (Or.inr rfl)
      have valueParse := parseOperand_tokens value fuel (.symbol ')') (.symbol ';' :: rest)
        (fun name mem => names name (by simp [StorageStmt.identifiers, mem]))
        (by simp only [StorageStmt.size] at enough; omega) (Or.inl rfl)
      simp only [StorageStmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseStorageStmt, slotParse, expectTokens, valueParse]

theorem StorageStmt.blockEnds_tokens (statement : StorageStmt) (names : statement.NamesOk)
    (rest : List Token) : blockEnds (statement.tokens ++ rest) = false := by
  cases statement with
  | plain statement => exact Stmt.blockEnds_tokens statement names rest
  | letCall => rfl
  | store => rfl

theorem parseStorageStmts_tokens : ∀ (statements : List StorageStmt) (fuel : Nat)
    (rest : List Token), StorageStmt.ListNamesOk statements →
    StorageStmt.listSize statements < fuel → blockEnds rest = true →
    parseStorageStmts fuel (StorageStmt.listTokens statements ++ rest) = some (statements, rest)
  | [], fuel + 1, rest, _, _, ends => by
      simp [StorageStmt.listTokens, parseStorageStmts, ends]
  | statement :: more, fuel + 1, rest, names, enough, ends => by
      have statementNames : statement.NamesOk :=
        fun name mem => names name (by simp [StorageStmt.listIdentifiers, mem])
      have moreNames : StorageStmt.ListNamesOk more :=
        fun name mem => names name (by simp [StorageStmt.listIdentifiers, mem])
      have statementParse := parseStorageStmt_tokens statement statementNames fuel
        (by simp only [StorageStmt.listSize] at enough; omega)
        (StorageStmt.listTokens more ++ rest)
      have moreParse := parseStorageStmts_tokens more fuel rest moreNames
        (by simp only [StorageStmt.listSize] at enough; omega) ends
      simp only [StorageStmt.listTokens, List.append_assoc]
      simp [parseStorageStmts, StorageStmt.blockEnds_tokens statement statementNames,
        statementParse, moreParse]

theorem parseStorageImport_tokens (aliases : List (String × String)) (rest : List Token) :
    parseStorageImport (storageImportTokens aliases ++ rest) = some (aliases, rest) := by
  cases aliases with
  | nil => simp [storageImportTokens, storageAliasTokens, parseStorageImport, expectTokens]
  | cons alias more =>
      have length := aliasTokens_length (alias :: more)
      simp only [storageImportTokens, storageAliasTokens, List.append_assoc, List.cons_append,
        List.nil_append]
      simp [parseStorageImport, expectTokens]
      rw [parseAliasList_tokens (alias :: more) _ _ (by simp) (by omega) rfl]
      simp [expectTokens]

/-! ### Sizes against tokens -/

theorem Operand.size_le_tokens (operand : Operand) : operand.size ≤ operand.tokens.length := by
  cases operand with
  | plain expression => exact Expr.size_le_tokens expression
  | operation op left right =>
      have := Expr.size_le_tokens left
      have := Expr.size_le_tokens right
      simp only [Operand.size, Operand.tokens, List.length_append, List.length_cons,
        List.length_nil]
      omega

theorem StorageStmt.size_lt_tokens (statement : StorageStmt) :
    statement.size < statement.tokens.length := by
  cases statement with
  | plain statement =>
      have := (Stmt.size_bounds (statement.size + 1)).1 statement (Nat.lt_succ_self _)
      simp only [StorageStmt.size, StorageStmt.tokens]
      omega
  | letCall identifier type callee op left right =>
      have := Expr.size_le_tokens left
      have := Expr.size_le_tokens right
      simp only [StorageStmt.size, StorageStmt.tokens, List.length_append, List.length_cons,
        List.length_nil]
      omega
  | store slot value =>
      have := Operand.size_le_tokens slot
      have := Operand.size_le_tokens value
      simp only [StorageStmt.size, StorageStmt.tokens, List.length_append, List.length_cons,
        List.length_nil]
      omega

theorem StorageStmt.listSize_le_tokens : (statements : List StorageStmt) →
    StorageStmt.listSize statements ≤ (StorageStmt.listTokens statements).length
  | [] => by simp [StorageStmt.listSize, StorageStmt.listTokens]
  | statement :: rest => by
      have := StorageStmt.size_lt_tokens statement
      have := StorageStmt.listSize_le_tokens rest
      simp only [StorageStmt.listSize, StorageStmt.listTokens, List.length_append]
      omega

theorem parseStorageFileWith_tokens (file : StorageFile) (names : file.NamesOk) (fuel : Nat)
    (functionsFuel : ∀ function ∈ file.functions,
      Stmt.listSize function.body < fuel ∧ function.result.size < fuel)
    (bodyFuel : StorageStmt.listSize file.method.body < fuel)
    (resultFuel : file.method.result.size < fuel) :
    parseStorageFileWith fuel file.tokens = some file := by
  obtain ⟨functionsOk, contractOk, methodOk, parametersOk, bodyOk, resultOk⟩ := names
  have resultParse := parseOperand_tokens file.method.result fuel (.symbol ')')
    [.symbol ';', .symbol '}', .symbol '}'] resultOk resultFuel (Or.inl rfl)
  have bodyParse := parseStorageStmts_tokens file.method.body fuel
    (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
      [.symbol ')', .symbol ';', .symbol '}', .symbol '}'])) bodyOk bodyFuel rfl
  have parametersParse := parseParameters_tokens file.method.parameters
    (signatureTokens ++ (StorageStmt.listTokens file.method.body ++
      (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
        [.symbol ')', .symbol ';', .symbol '}', .symbol '}'])))) parametersOk rfl
  have functionsLength := functions_length_le_tokens file.functions
  have functionsParse := parseFunctions_tokens file.functions (file.tokens.length + 1) fuel
    (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
      .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
        (signatureTokens ++ (StorageStmt.listTokens file.method.body ++
          (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
            [.symbol ')', .symbol ';', .symbol '}', .symbol '}']))))))
    (fun function mem => ⟨functionsOk function mem, functionsFuel function mem⟩)
    (by simp only [StorageFile.tokens, List.length_append] at functionsLength ⊢; omega)
    (by simp)
  have importParse := parseStorageImport_tokens file.opcodeAliases
    (file.functions.flatMap FunctionDecl.tokens ++
      (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
        .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
          (signatureTokens ++ (StorageStmt.listTokens file.method.body ++
            (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
              [.symbol ')', .symbol ';', .symbol '}', .symbol '}'])))))))
  unfold parseStorageFileWith
  conv => lhs; arg 1; rw [StorageFile.tokens]
  simp only [List.append_assoc, List.cons_append, List.nil_append, expectTokens_append,
    Option.bind_eq_bind, Option.bind_some]
  rw [importParse]
  simp only [Option.bind_some]
  rw [functionsParse]
  simp [expectTokens, parseName_cons contractOk, parseName_cons methodOk, parametersParse,
    expectTokens_append, bodyParse, resultParse]

/-- **Parser round trip.** Parsing the tokens of a storage file with
non-reserved names returns that file. -/
theorem parseStorageFile_tokens (file : StorageFile) (names : file.NamesOk) :
    parseStorageFile file.tokens = some file := by
  have bodySize := StorageStmt.listSize_le_tokens file.method.body
  have resultSize := Operand.size_le_tokens file.method.result
  apply parseStorageFileWith_tokens file names
  · intro function mem
    have := functions_sizes_le_tokens mem
    simp only [StorageFile.tokens, List.length_append]
    omega
  · simp only [StorageFile.tokens, List.length_append] at bodySize ⊢
    omega
  · simp only [StorageFile.tokens, List.length_append, List.length_cons] at resultSize ⊢
    omega

/-! ### Printed pieces -/

def Operand.pieces : Operand → List Piece
  | .plain expression => expression.pieces
  | .operation op left right => left.pieces ++ [space, .token op.token, space] ++ right.pieces

theorem Operand.print_toList (operand : Operand) :
    operand.print.toList = render operand.pieces := by
  cases operand with
  | plain expression => exact Expr.print_toList expression
  | operation op left right =>
      simp [Operand.print, Operand.pieces, render_append, render, Piece.chars, Token.chars, space,
        Expr.print_toList, BinaryOp.spelling_toList]

theorem Operand.tokensOf_pieces (operand : Operand) :
    tokensOf operand.pieces = operand.tokens := by
  cases operand with
  | plain expression => exact Expr.tokensOf_pieces expression
  | operation op left right =>
      simp [Operand.pieces, Operand.tokens, tokensOf_append, tokensOf, space,
        Expr.tokensOf_pieces]

/-- An operand followed by a piece that is safe on its left is separated. -/
theorem Operand.separated_append (operand : Operand)
    (valid : ∀ name ∈ operand.identifiers, ValidIdentifier name) (rest : List Piece)
    (separated : Separated rest) (safe : ∀ next ∈ rest.head?, next.SafeLeft) :
    Separated (operand.pieces ++ rest) := by
  cases operand with
  | plain expression => exact Expr.separated_append expression valid rest separated safe
  | operation op left right =>
      have rightPart := Expr.separated_append right
        (fun name mem => valid name (List.mem_append_right _ mem)) rest separated safe
      have middle : Separated (space :: .token op.token :: space :: (right.pieces ++ rest)) :=
        Separated.cons_space (Separated.cons_safe (BinaryOp.token_valid op).1
          (BinaryOp.token_valid op).2 (Separated.cons_space rightPart))
      have leftPart := Expr.separated_append left
        (fun name mem => valid name (List.mem_append_left _ mem)) _ middle
        (fun next same => by cases same; exact space_safeLeft)
      simpa [Operand.pieces, List.append_assoc] using leftPart

def StorageStmt.linePieces (indent : Nat) : StorageStmt → List (List Piece)
  | .plain statement => statement.linePieces indent
  | .letCall identifier type callee op left right =>
      [blanks indent ++ [word "let", space, word identifier, sym ':', space] ++ type.pieces ++
        [space, sym '=', space, word callee, sym '('] ++
        (Operand.operation op left right).pieces ++ [sym ')', sym ';']]
  | .store slot value =>
      [blanks indent ++ [word "sstore", sym '('] ++ slot.pieces ++ [sym ',', space] ++
        value.pieces ++ [sym ')', sym ';']]

def StorageStmt.listLinePieces (indent : Nat) : List StorageStmt → List (List Piece)
  | [] => []
  | statement :: rest => statement.linePieces indent ++ StorageStmt.listLinePieces indent rest

theorem StorageStmt.lines_toList (indent : Nat) : (statement : StorageStmt) →
    (statement.lines indent).map String.toList = (statement.linePieces indent).map render
  | .plain statement => Stmt.lines_toList indent statement
  | .letCall identifier type callee op left right => by
      simp [StorageStmt.lines, StorageStmt.linePieces, indentLine_toList, render_append,
        render_blanks, render, Piece.chars, Token.chars, word, sym, space,
        LocalType.spelling_toList, Operand.print_toList]
  | .store slot value => by
      simp [StorageStmt.lines, StorageStmt.linePieces, indentLine_toList, render_append,
        render_blanks, render, Piece.chars, Token.chars, word, sym, space, Operand.print_toList]

theorem StorageStmt.listLines_toList (indent : Nat) : (statements : List StorageStmt) →
    (StorageStmt.listLines indent statements).map String.toList =
      (StorageStmt.listLinePieces indent statements).map render
  | [] => rfl
  | statement :: rest => by
      simp [StorageStmt.listLines, StorageStmt.listLinePieces,
        StorageStmt.lines_toList indent statement, StorageStmt.listLines_toList indent rest]

theorem StorageStmt.linePieces_tokens (indent : Nat) : (statement : StorageStmt) →
    ((statement.linePieces indent).map tokensOf).flatten = statement.tokens
  | .plain statement => Stmt.linePieces_tokens indent statement
  | .letCall identifier type callee op left right => by
      simp [StorageStmt.linePieces, StorageStmt.tokens, tokensOf_append, tokensOf_blanks,
        tokensOf, word, sym, space, LocalType.tokensOf_pieces, Operand.tokensOf_pieces,
        Operand.tokens]
  | .store slot value => by
      simp [StorageStmt.linePieces, StorageStmt.tokens, tokensOf_append, tokensOf_blanks,
        tokensOf, word, sym, space, Operand.tokensOf_pieces]

theorem StorageStmt.listLinePieces_tokens (indent : Nat) : (statements : List StorageStmt) →
    ((StorageStmt.listLinePieces indent statements).map tokensOf).flatten =
      StorageStmt.listTokens statements
  | [] => rfl
  | statement :: rest => by
      simp [StorageStmt.listLinePieces, StorageStmt.listTokens,
        StorageStmt.linePieces_tokens indent statement,
        StorageStmt.listLinePieces_tokens indent rest]

theorem StorageStmt.linePieces_separated (indent : Nat) : (statement : StorageStmt) →
    (∀ name ∈ statement.identifiers, ValidIdentifier name) →
    ∀ line ∈ statement.linePieces indent, Separated line
  | .plain statement, valid, line, mem =>
      Stmt.linePieces_separated indent statement valid line mem
  | .letCall identifier type callee op left right, valid, line, mem => by
      simp only [StorageStmt.linePieces, List.mem_singleton] at mem
      subst mem
      have operation := Operand.separated_append (.operation op left right)
        (fun name mem => valid name (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem)))
        [sym ')', sym ';'] (Separated.cons_sym (by decide) (sym_valid (by decide)))
        (head_sym (by decide))
      have calleePart : Separated (word callee :: sym '(' ::
          ((Operand.operation op left right).pieces ++ [sym ')', sym ';'])) :=
        Separated.cons_word (valid callee (by simp [StorageStmt.identifiers]))
          (Separated.cons_sym (by decide) operation) (head_sym (by decide))
      have typePart := LocalType.separated_append type _ (Separated.cons_space
        (Separated.cons_equal (Separated.cons_space calleePart) (fun next same => by
          cases same; rfl))) head_space
      simp only [List.append_assoc, List.cons_append, List.nil_append] at typePart ⊢
      exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
        (Separated.cons_space (Separated.cons_word
          (valid identifier (by simp [StorageStmt.identifiers]))
          (Separated.cons_sym (by decide) (Separated.cons_space typePart))
          (head_sym (by decide))))
        head_space)
  | .store slot value, valid, line, mem => by
      simp only [StorageStmt.linePieces, List.mem_singleton] at mem
      subst mem
      have valuePart := Operand.separated_append value
        (fun name mem => valid name (List.mem_append_right _ mem))
        [sym ')', sym ';'] (Separated.cons_sym (by decide) (sym_valid (by decide)))
        (head_sym (by decide))
      have slotPart := Operand.separated_append slot
        (fun name mem => valid name (List.mem_append_left _ mem))
        (sym ',' :: space :: (value.pieces ++ [sym ')', sym ';']))
        (Separated.cons_sym (by decide) (Separated.cons_space valuePart)) (head_sym (by decide))
      simp only [List.append_assoc, List.cons_append, List.nil_append] at slotPart ⊢
      exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
        (Separated.cons_sym (by decide) slotPart) (head_sym (by decide)))

theorem StorageStmt.listLinePieces_separated (indent : Nat) : (statements : List StorageStmt) →
    (∀ name ∈ StorageStmt.listIdentifiers statements, ValidIdentifier name) →
    ∀ line ∈ StorageStmt.listLinePieces indent statements, Separated line
  | [], _, _, mem => by simp [StorageStmt.listLinePieces] at mem
  | statement :: rest, valid, line, mem => by
      simp only [StorageStmt.listLinePieces, List.mem_append] at mem
      rcases mem with mem | mem
      · exact StorageStmt.linePieces_separated indent statement
          (fun name found => valid name (by simp [StorageStmt.listIdentifiers, found])) line mem
      · exact StorageStmt.listLinePieces_separated indent rest
          (fun name found => valid name (by simp [StorageStmt.listIdentifiers, found])) line mem

/-- The aliases after `sload, sstore`, after one more comma. -/
def storageAliasPieces : List (String × String) → List Piece
  | [] => []
  | alias :: rest => sym ',' :: space :: aliasPieces (alias :: rest)

def storageImportPieces (aliases : List (String × String)) : List Piece :=
  [word "import", space, sym '{', word "sload", sym ',', space, word "sstore"] ++
    storageAliasPieces aliases ++
    [sym '}', space, word "from", space, word "std", sym '.', word "opcodes", sym ';']

theorem storageImportLine_toList (aliases : List (String × String)) :
    (storageImportLine aliases).toList = render (storageImportPieces aliases) := by
  cases aliases with
  | nil =>
      simp [storageImportLine, storageImportPieces, storageAliasPieces,
        String.intercalate_cons_cons, render, Piece.chars, Token.chars, word, sym, space]
  | cons alias more =>
      have tail := aliasText_toList (alias :: more)
      simp only [List.map_cons] at tail
      simp only [storageImportLine, List.cons_append, List.nil_append, List.map_cons]
      rw [String.intercalate_cons_cons, String.intercalate_cons_cons]
      simp only [String.toList_append, tail]
      simp [storageImportPieces, storageAliasPieces, render_append, render, Piece.chars,
        Token.chars, word, sym, space]

theorem storageImportPieces_tokens (aliases : List (String × String)) :
    tokensOf (storageImportPieces aliases) = storageImportTokens aliases := by
  cases aliases <;>
    simp [storageImportPieces, storageAliasPieces, storageImportTokens, storageAliasTokens,
      tokensOf_append, tokensOf, word, sym, space, aliasPieces_tokens]

theorem storageImportPieces_separated (aliases : List (String × String))
    (valid : ∀ alias ∈ aliases, ValidIdentifier alias.1 ∧ ValidIdentifier alias.2) :
    Separated (storageImportPieces aliases) := by
  have closing : Separated [sym '}', space, word "from", space, word "std", sym '.',
      word "opcodes", sym ';'] :=
    Separated.cons_sym (by decide) (Separated.cons_space (Separated.cons_word
      (keyword_valid (by decide)) (Separated.cons_space (Separated.cons_word
        (keyword_valid (by decide)) (Separated.cons_sym (by decide) (Separated.cons_word
          (keyword_valid (by decide)) (sym_valid (by decide)) (head_sym (by decide))))
        (head_sym (by decide)))) head_space))
  have middle : Separated (storageAliasPieces aliases ++ [sym '}', space, word "from", space,
        word "std", sym '.', word "opcodes", sym ';']) ∧
      ∀ next ∈ (storageAliasPieces aliases ++ [sym '}', space, word "from", space,
        word "std", sym '.', word "opcodes", sym ';']).head?, next.SafeLeft := by
    cases aliases with
    | nil => exact ⟨closing, head_sym (by decide)⟩
    | cons alias more =>
        exact ⟨Separated.cons_sym (by decide) (Separated.cons_space
          (aliasPieces_separated (alias :: more) valid _ closing (head_sym (by decide)))),
          head_sym (by decide)⟩
  simp only [storageImportPieces, List.cons_append, List.nil_append]
  exact Separated.cons_word (keyword_valid (by decide)) (Separated.cons_space
    (Separated.cons_sym (by decide) (Separated.cons_word (keyword_valid (by decide))
      (Separated.cons_sym (by decide) (Separated.cons_space (Separated.cons_word
        (keyword_valid (by decide)) middle.1 middle.2))) (head_sym (by decide)))))
    head_space

def StorageFile.linePieces (file : StorageFile) : List (List Piece) :=
  [[word "import", space, sym '*', space, word "from", space, word "std", sym ';'],
    [word "import", space, sym '*', space, word "from", space, word "std", sym '.',
      word "dispatch", sym ';']] ++
  [storageImportPieces file.opcodeAliases] ++ [[]] ++
  file.functions.flatMap FunctionDecl.linePieces ++
  [[word "contract", space, word file.contract, space, sym '{'],
    blanks 4 ++ [word "function", space, word file.method.name, sym '('] ++
      parameterPieces file.method.parameters ++
      [sym ')', space, word "public", space, word "returns", space, sym '(', word "uint256",
        sym ')', space, sym '{']] ++
  StorageStmt.listLinePieces 8 file.method.body ++
  [blanks 8 ++ [word "return", space, word "uint256", sym '('] ++ file.method.result.pieces ++
      [sym ')', sym ';'],
    blanks 4 ++ [sym '}'], [sym '}']]

theorem StorageFile.lines_toList (file : StorageFile) :
    file.lines.map String.toList = file.linePieces.map render := by
  simp only [StorageFile.lines, StorageFile.linePieces, List.map_append, functions_lines_toList]
  simp [StorageStmt.listLines_toList, parameterText_toList, Operand.print_toList,
    storageImportLine_toList, render_append, render_blanks, render, Piece.chars, Token.chars,
    word, sym, space]

theorem StorageFile.linePieces_tokens (file : StorageFile) :
    (file.linePieces.map tokensOf).flatten = file.tokens := by
  simp only [StorageFile.linePieces, StorageFile.tokens, List.map_append, List.flatten_append,
    functions_linePieces_tokens]
  simp [importTokens, signatureTokens, StorageStmt.listLinePieces_tokens,
    parameterPieces_tokens, Operand.tokensOf_pieces, storageImportPieces_tokens,
    tokensOf_append, tokensOf_blanks, tokensOf, word, sym, space]

/-- Every identifier of the storage file is lexically valid. -/
def StorageFile.IdentifiersValid (file : StorageFile) : Prop :=
  (∀ alias ∈ file.opcodeAliases, ValidIdentifier alias.1 ∧ ValidIdentifier alias.2) ∧
    (∀ function ∈ file.functions, ∀ name ∈ function.identifiers, ValidIdentifier name) ∧
    ValidIdentifier file.contract ∧ ValidIdentifier file.method.name ∧
    (∀ parameter ∈ file.method.parameters, ValidIdentifier parameter) ∧
    (∀ name ∈ StorageStmt.listIdentifiers file.method.body, ValidIdentifier name) ∧
    (∀ name ∈ file.method.result.identifiers, ValidIdentifier name)

/-- The storage file without aliases, method body or returned operand. Its
lines are the storage file's import, function, contract and closing lines. -/
def StorageFile.skeleton (file : StorageFile) : SourceFile where
  opcodeAliases := []
  functions := file.functions
  contract := file.contract
  method := {
    name := file.method.name, parameters := file.method.parameters, body := [],
    result := .number 0 }

theorem StorageFile.linePieces_separated (file : StorageFile) (valid : file.IdentifiersValid) :
    ∀ line ∈ file.linePieces, Separated line := by
  obtain ⟨aliasesValid, functionsValid, contractValid, methodValid, parametersValid, bodyValid,
    resultValid⟩ := valid
  have skeleton := file.skeleton.linePieces_separated ⟨by simp [StorageFile.skeleton],
    functionsValid, contractValid, methodValid, parametersValid,
    by simp [StorageFile.skeleton, Stmt.listIdentifiers],
    by simp [StorageFile.skeleton, Expr.identifiers]⟩
  intro line mem
  unfold StorageFile.linePieces at mem
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
              exact storageImportPieces_separated _ aliasesValid
          · simp only [List.mem_singleton] at mem
            subst mem
            trivial
        · exact skeleton line (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_right _ mem))))
      · exact skeleton line (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ mem)))
    · exact StorageStmt.listLinePieces_separated 8 file.method.body bodyValid line mem
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

theorem StorageFile.print_toList (file : StorageFile) :
    file.print.toList = render (joinLines file.linePieces) := by
  rw [StorageFile.print, String.toList_append, String.toList_intercalate, joinLines,
    render_append, render_intercalate, StorageFile.lines_toList]
  rfl

/-- **Text round trip.** The printed text of a storage file with lexically
valid, non-reserved names parses back to that file. -/
theorem parseStorageSource_print (file : StorageFile) (names : file.NamesOk)
    (valid : file.IdentifiersValid) : parseStorageSource file.print = some file := by
  rw [parseStorageSource, StorageFile.print_toList,
    lex_render (joinLines_separated _ (file.linePieces_separated valid)), Option.bind_some,
    tokensOf_joinLines, StorageFile.linePieces_tokens]
  exact parseStorageFile_tokens file names

/-- The meaning of a printed storage file's text is the meaning of the file. -/
theorem storageSourceCall_print (file : StorageFile) (names : file.NamesOk)
    (valid : file.IdentifiersValid) (storage : Storage) (method : String)
    (arguments : List Nat) :
    storageSourceCall file.print storage method arguments =
      file.call storage method arguments := by
  simp [storageSourceCall, parseStorageSource_print file names valid]

end Solcore.Synthesis.Source.ScalarMeaning
