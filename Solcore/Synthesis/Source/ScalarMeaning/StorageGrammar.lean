import Solcore.Synthesis.Source.ScalarMeaning.FragmentSemantics
import Solcore.Synthesis.Source.ScalarMeaning.Grammar
import Solcore.Synthesis.Source.ScalarMeaning.LogSemantics

/-!
# Storage, rollback, keyed and log text

The grammars of the stateful fragments. Main declarations: `parseStorageSource`,
`storageSourceCall`, `parseRollbackSource`, `rollbackSourceCall`, `parseKeyedSource`,
`keyedSourceCall`, `parseLogSource`, `logSourceCall`. Main theorems: `parseStorageSource_print`,
`parseRollbackSource_print`, `parseKeyedSource_print`, `parseLogSource_print`.
-/

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.StorageText
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
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.RollbackText
/-! Text of rollback programs. `parseRollbackSource` lexes a complete text as
`parseSource` does and parses it with the storage grammar, extended by the
rollback import line, operation `let`s and the revert block. Each extension is
recognized from its first tokens: the revert block and an operation `let` go
on with an infix operator after the first expression of their condition or
value, where a loop-free `if` condition ends with `)`, a loop-free `let` value
with `;`, and the value of a call `let` is no complete expression. The printed
text of every rollback file with valid, non-reserved names parses back to that
file. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

/-! ### Tokens -/

def RollbackStmt.tokens : RollbackStmt → List Token
  | .storage statement => statement.tokens
  | .letOperation identifier type op left right =>
      [.ident "let", .ident identifier, .symbol ':'] ++ type.tokens ++ [.symbol '='] ++
        left.tokens ++ [op.token] ++ right.tokens ++ [.symbol ';']
  | .revertIf op left right offset value dataOffset size =>
      [.ident "if", .symbol '('] ++ left.tokens ++ [op.token] ++ right.tokens ++
        [.symbol ')', .symbol '{', .ident "mstore", .symbol '('] ++ offset.tokens ++
        [.symbol ','] ++ value.tokens ++
        [.symbol ')', .symbol ';', .ident "revert_", .symbol '('] ++ dataOffset.tokens ++
        [.symbol ','] ++ size.tokens ++ [.symbol ')', .symbol ';', .symbol '}']

def RollbackStmt.listTokens : List RollbackStmt → List Token
  | [] => []
  | statement :: rest => statement.tokens ++ RollbackStmt.listTokens rest

def rollbackImportTokens (aliases : List (String × String)) : List Token :=
  [.ident "import", .symbol '{', .ident "sload", .symbol ',', .ident "sstore", .symbol ',',
    .ident "mstore", .symbol ',', .ident "revert_"] ++ storageAliasTokens aliases ++
    [.symbol '}', .ident "from", .ident "std", .symbol '.', .ident "opcodes", .symbol ';']

def RollbackFile.tokens (file : RollbackFile) : List Token :=
  importTokens ++ rollbackImportTokens file.opcodeAliases ++
    file.functions.flatMap FunctionDecl.tokens ++
    [.ident "contract", .ident file.contract, .symbol '{', .ident "function",
      .ident file.method.name, .symbol '('] ++ parameterTokens file.method.parameters ++
    signatureTokens ++ RollbackStmt.listTokens file.method.body ++
    [.ident "return", .ident "uint256", .symbol '('] ++ file.method.result.tokens ++
    [.symbol ')', .symbol ';', .symbol '}', .symbol '}']

/-! ### Parser -/

/-- The revert block, when an infix operator follows the first expression of
its condition. -/
def parseRevertIf (fuel : Nat) (tokens : List Token) : Option (RollbackStmt × List Token) := do
  let rest ← expectTokens [.ident "if", .symbol '('] tokens
  let (left, rest) ← parseExpr fuel rest
  match rest with
  | next :: rest => do
      let op ← parseBinaryOp? next
      let (right, rest) ← parseExpr fuel rest
      let rest ← expectTokens [.symbol ')', .symbol '{', .ident "mstore", .symbol '('] rest
      let (offset, rest) ← parseOperand fuel rest
      let rest ← expectTokens [.symbol ','] rest
      let (value, rest) ← parseOperand fuel rest
      let rest ← expectTokens [.symbol ')', .symbol ';', .ident "revert_", .symbol '('] rest
      let (dataOffset, rest) ← parseOperand fuel rest
      let rest ← expectTokens [.symbol ','] rest
      let (size, rest) ← parseOperand fuel rest
      let rest ← expectTokens [.symbol ')', .symbol ';', .symbol '}'] rest
      some (.revertIf op left right offset value dataOffset size, rest)
  | [] => none

/-- `let x: T = a op b;`, when an infix operator follows the first expression of
the value. -/
def parseLetOperation (fuel : Nat) (tokens : List Token) :
    Option (RollbackStmt × List Token) := do
  let rest ← expectTokens [.ident "let"] tokens
  let (identifier, rest) ← parseName rest
  let rest ← expectTokens [.symbol ':'] rest
  let (type, rest) ← parseLocalType rest
  let rest ← expectTokens [.symbol '='] rest
  let (left, rest) ← parseExpr fuel rest
  match rest with
  | next :: rest => do
      let op ← parseBinaryOp? next
      let (right, rest) ← parseExpr fuel rest
      let rest ← expectTokens [.symbol ';'] rest
      some (.letOperation identifier type op left right, rest)
  | [] => none

/-- A revert block, an operation `let`, or otherwise a storage statement. -/
def parseRollbackStmt (fuel : Nat) (tokens : List Token) :
    Option (RollbackStmt × List Token) :=
  match parseRevertIf fuel tokens with
  | some parsed => some parsed
  | none =>
      match parseLetOperation fuel tokens with
      | some parsed => some parsed
      | none => (parseStorageStmt fuel tokens).map fun parsed => (.storage parsed.1, parsed.2)

def parseRollbackStmts : Nat → List Token → Option (List RollbackStmt × List Token)
  | 0, _ => none
  | fuel + 1, tokens =>
      if blockEnds tokens then some ([], tokens)
      else do
        let (statement, rest) ← parseRollbackStmt fuel tokens
        let (statements, rest) ← parseRollbackStmts fuel rest
        some (statement :: statements, rest)

/-- `import {sload, sstore, mstore, revert_, opcode as alias, ...} from std.opcodes;` -/
def parseRollbackImport (tokens : List Token) :
    Option (List (String × String) × List Token) := do
  let rest ← expectTokens
    [.ident "import", .symbol '{', .ident "sload", .symbol ',', .ident "sstore", .symbol ',',
      .ident "mstore", .symbol ',', .ident "revert_"] tokens
  let (aliases, rest) ←
    if rest.head? = some (.symbol ',') then parseAliasList rest.length rest.tail
    else some ([], rest)
  let rest ← expectTokens
    [.symbol '}', .ident "from", .ident "std", .symbol '.', .ident "opcodes", .symbol ';'] rest
  some (aliases, rest)

/-- `parseStorageFileWith` with the rollback import line and a rollback method
body. -/
def parseRollbackFileWith (fuel : Nat) (tokens : List Token) : Option RollbackFile := do
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
  let (body, rest) ← parseRollbackStmts fuel rest
  let rest ← expectTokens [.ident "return", .ident "uint256", .symbol '('] rest
  let (result, rest) ← parseOperand fuel rest
  let rest ← expectTokens [.symbol ')', .symbol ';', .symbol '}', .symbol '}'] rest
  if rest = [] then
    some ⟨opcodeAliases, functions, contract, ⟨method, parameters, body, result⟩⟩
  else none

/-- Parse a complete token stream; one more than its length bounds nesting. -/
def parseRollbackFile (tokens : List Token) : Option RollbackFile :=
  parseRollbackFileWith (tokens.length + 1) tokens

def parseRollbackSource (source : String) : Option RollbackFile :=
  (lex source.toList).bind parseRollbackFile

/-- The outcome of calling `method` from `storage` on the contract written in
`source`, read as a rollback program. -/
def rollbackSourceCall (source : String) (storage : Storage) (method : String)
    (arguments : List Nat) : Option RollbackOutcome :=
  (parseRollbackSource source).bind fun file => file.call storage method arguments

/-! ### Sizes and names -/

def RollbackStmt.size : RollbackStmt → Nat
  | .storage statement => statement.size
  | .letOperation _ _ _ left right => left.size + right.size
  | .revertIf _ left right offset value dataOffset size =>
      left.size + right.size + offset.size + value.size + dataOffset.size + size.size

def RollbackStmt.listSize : List RollbackStmt → Nat
  | [] => 0
  | statement :: rest => statement.size + RollbackStmt.listSize rest + 1

def RollbackStmt.NamesOk (statement : RollbackStmt) : Prop :=
  ∀ name ∈ statement.identifiers, isReserved name = false

def RollbackStmt.ListNamesOk (statements : List RollbackStmt) : Prop :=
  ∀ name ∈ RollbackStmt.listIdentifiers statements, isReserved name = false

def RollbackFile.NamesOk (file : RollbackFile) : Prop :=
  (∀ function ∈ file.functions, function.NamesOk) ∧
    isReserved file.contract = false ∧ isReserved file.method.name = false ∧
    (∀ parameter ∈ file.method.parameters, isReserved parameter = false) ∧
    RollbackStmt.ListNamesOk file.method.body ∧ file.method.result.NamesOk

/-! ### Round trip -/

theorem Expr.size_pos (expression : Expr) : 0 < expression.size := by
  cases expression <;> simp [Expr.size]

theorem parseBinaryOp?_semicolon : parseBinaryOp? (.symbol ';') = none := by decide

theorem parseLetOperation_tokens (identifier : String) (type : LocalType) (op : BinaryOp)
    (left right : Expr) (fuel : Nat) (rest : List Token)
    (names : (RollbackStmt.letOperation identifier type op left right).NamesOk)
    (enough : (RollbackStmt.letOperation identifier type op left right).size < fuel) :
    parseLetOperation fuel ((RollbackStmt.letOperation identifier type op left right).tokens ++
      rest) = some (.letOperation identifier type op left right, rest) := by
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
  simp [parseLetOperation, expectTokens, parseName_cons identifierOk, LocalType.parse_tokens,
    leftParse, BinaryOp.parse_token, rightParse]

theorem parseRevertIf_tokens (op : BinaryOp) (left right : Expr)
    (offset value dataOffset size : Operand) (fuel : Nat) (rest : List Token)
    (names : (RollbackStmt.revertIf op left right offset value dataOffset size).NamesOk)
    (enough : (RollbackStmt.revertIf op left right offset value dataOffset size).size < fuel) :
    parseRevertIf fuel ((RollbackStmt.revertIf op left right offset value dataOffset size).tokens ++
      rest) = some (.revertIf op left right offset value dataOffset size, rest) := by
  have leftParse := parseExpr_tokens left fuel (op.token :: (right.tokens ++ .symbol ')' ::
      .symbol '{' :: .ident "mstore" :: .symbol '(' :: (offset.tokens ++ .symbol ',' ::
        (value.tokens ++ .symbol ')' :: .symbol ';' :: .ident "revert_" :: .symbol '(' ::
          (dataOffset.tokens ++ .symbol ',' :: (size.tokens ++
            .symbol ')' :: .symbol ';' :: .symbol '}' :: rest))))))
    (fun name mem => names name (by simp [RollbackStmt.identifiers, mem]))
    (by simp only [RollbackStmt.size] at enough; omega)
    (by simpa using BinaryOp.token_ne_open op)
  have rightParse := parseExpr_tokens right fuel (.symbol ')' ::
      .symbol '{' :: .ident "mstore" :: .symbol '(' :: (offset.tokens ++ .symbol ',' ::
        (value.tokens ++ .symbol ')' :: .symbol ';' :: .ident "revert_" :: .symbol '(' ::
          (dataOffset.tokens ++ .symbol ',' :: (size.tokens ++
            .symbol ')' :: .symbol ';' :: .symbol '}' :: rest)))))
    (fun name mem => names name (by simp [RollbackStmt.identifiers, mem]))
    (by simp only [RollbackStmt.size] at enough; omega) (by simp)
  have offsetParse := parseOperand_tokens offset fuel (.symbol ',')
    (value.tokens ++ .symbol ')' :: .symbol ';' :: .ident "revert_" :: .symbol '(' ::
      (dataOffset.tokens ++ .symbol ',' :: (size.tokens ++
        .symbol ')' :: .symbol ';' :: .symbol '}' :: rest)))
    (fun name mem => names name (by simp [RollbackStmt.identifiers, mem]))
    (by simp only [RollbackStmt.size] at enough; omega) (Or.inr rfl)
  have valueParse := parseOperand_tokens value fuel (.symbol ')')
    (.symbol ';' :: .ident "revert_" :: .symbol '(' :: (dataOffset.tokens ++ .symbol ',' ::
      (size.tokens ++ .symbol ')' :: .symbol ';' :: .symbol '}' :: rest)))
    (fun name mem => names name (by simp [RollbackStmt.identifiers, mem]))
    (by simp only [RollbackStmt.size] at enough; omega) (Or.inl rfl)
  have dataOffsetParse := parseOperand_tokens dataOffset fuel (.symbol ',')
    (size.tokens ++ .symbol ')' :: .symbol ';' :: .symbol '}' :: rest)
    (fun name mem => names name (by simp [RollbackStmt.identifiers, mem]))
    (by simp only [RollbackStmt.size] at enough; omega) (Or.inr rfl)
  have sizeParse := parseOperand_tokens size fuel (.symbol ')')
    (.symbol ';' :: .symbol '}' :: rest)
    (fun name mem => names name (by simp [RollbackStmt.identifiers, mem]))
    (by simp only [RollbackStmt.size] at enough; omega) (Or.inl rfl)
  simp only [RollbackStmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
  simp [parseRevertIf, expectTokens, leftParse, BinaryOp.parse_token, rightParse, offsetParse,
    valueParse, dataOffsetParse, sizeParse]

/-- An operator never ends the first argument of a loop-free call, so a call
whose argument is an operation is no complete expression. -/
theorem parseExpr_call_operation (callee : String) (calleeOk : isReserved callee = false)
    (op : BinaryOp) (left : Expr) (names : left.NamesOk) (fuel : Nat)
    (enough : left.size + 1 < fuel) (rest : List Token) :
    parseExpr fuel (.ident callee :: .symbol '(' :: (left.tokens ++ op.token :: rest)) = none := by
  obtain ⟨smaller, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
  have leftParse := parseExpr_tokens left smaller (op.token :: rest) names (by omega)
    (by simpa using BinaryOp.token_ne_open op)
  have reserved := not_reserved_names calleeOk
  cases op <;>
    simp only [BinaryOp.token] at leftParse <;>
    simp [parseExpr, reserved.1, reserved.2.1, reserved.2.2.1, reserved.2.2.2.1,
      reserved.2.2.2.2.1, reserved.2.2.2.2.2, calleeOk, leftParse, BinaryOp.token]

/-- No storage statement reads as an operation `let`. -/
theorem parseLetOperation_storage (statement : StorageStmt) (names : statement.NamesOk)
    (fuel : Nat) (enough : statement.size < fuel) (rest : List Token) :
    parseLetOperation fuel (statement.tokens ++ rest) = none := by
  cases statement with
  | plain statement =>
      cases statement with
      | letDecl identifier type initializer =>
          have identifierOk : isReserved identifier = false :=
            names identifier (by simp [StorageStmt.identifiers, Stmt.identifiers])
          have initializerParse := parseExpr_tokens initializer fuel (.symbol ';' :: rest)
            (fun name mem => names name (by
              simp [StorageStmt.identifiers, Stmt.identifiers, mem]))
            (by simp only [StorageStmt.size, Stmt.size] at enough; omega) (by simp)
          simp only [StorageStmt.tokens, Stmt.tokens, List.append_assoc, List.cons_append,
            List.nil_append]
          simp [parseLetOperation, expectTokens, parseName_cons identifierOk,
            LocalType.parse_tokens, initializerParse, parseBinaryOp?_semicolon]
      | assign identifier value =>
          have identifierOk : isReserved identifier = false :=
            names identifier (by simp [StorageStmt.identifiers, Stmt.identifiers])
          have notLet : "let" ≠ identifier :=
            fun same => (not_reserved_ne identifierOk).1 same.symm
          simp [StorageStmt.tokens, Stmt.tokens, parseLetOperation, expectTokens, notLet]
      | ifElse => simp [StorageStmt.tokens, Stmt.tokens, parseLetOperation, expectTokens]
      | matchPair => simp [StorageStmt.tokens, Stmt.tokens, parseLetOperation, expectTokens]
      | matchSum => simp [StorageStmt.tokens, Stmt.tokens, parseLetOperation, expectTokens]
  | letCall identifier type callee op left right =>
      have identifierOk : isReserved identifier = false :=
        names identifier (by simp [StorageStmt.identifiers])
      have calleeOk : isReserved callee = false :=
        names callee (by simp [StorageStmt.identifiers])
      have rightSize := Expr.size_pos right
      have callParse := parseExpr_call_operation callee calleeOk op left
        (fun name mem => names name (by simp [StorageStmt.identifiers, mem])) fuel
        (by simp only [StorageStmt.size] at enough; omega)
        (right.tokens ++ .symbol ')' :: .symbol ';' :: rest)
      simp only [StorageStmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseLetOperation, expectTokens, parseName_cons identifierOk, LocalType.parse_tokens,
        callParse]
  | store slot value => simp [StorageStmt.tokens, parseLetOperation, expectTokens]

/-- No storage statement and no operation `let` reads as a revert block. -/
theorem parseRevertIf_storage (statement : StorageStmt) (names : statement.NamesOk)
    (fuel : Nat) (enough : statement.size < fuel) (rest : List Token) :
    parseRevertIf fuel (statement.tokens ++ rest) = none := by
  cases statement with
  | plain statement =>
      cases statement with
      | ifElse condition thenBlock elseBlock =>
          have conditionParse := parseExpr_tokens condition fuel
            (.symbol ')' :: .symbol '{' :: (Stmt.listTokens thenBlock ++
              .symbol '}' :: .ident "else" :: .symbol '{' :: (Stmt.listTokens elseBlock ++
                .symbol '}' :: rest)))
            (fun name mem => names name (by
              simp [StorageStmt.identifiers, Stmt.identifiers, mem]))
            (by simp only [StorageStmt.size, Stmt.size] at enough; omega) (by simp)
          simp only [StorageStmt.tokens, Stmt.tokens, List.append_assoc, List.cons_append,
            List.nil_append]
          simp [parseRevertIf, expectTokens, conditionParse, parseBinaryOp?_close]
      | letDecl => simp [StorageStmt.tokens, Stmt.tokens, parseRevertIf, expectTokens]
      | assign identifier value =>
          have identifierOk : isReserved identifier = false :=
            names identifier (by simp [StorageStmt.identifiers, Stmt.identifiers])
          have notIf : "if" ≠ identifier :=
            fun same => (not_reserved_ne identifierOk).2.1 same.symm
          simp [StorageStmt.tokens, Stmt.tokens, parseRevertIf, expectTokens, notIf]
      | matchPair => simp [StorageStmt.tokens, Stmt.tokens, parseRevertIf, expectTokens]
      | matchSum => simp [StorageStmt.tokens, Stmt.tokens, parseRevertIf, expectTokens]
  | letCall => simp [StorageStmt.tokens, parseRevertIf, expectTokens]
  | store => simp [StorageStmt.tokens, parseRevertIf, expectTokens]

theorem parseRollbackStmt_tokens (statement : RollbackStmt) (names : statement.NamesOk)
    (fuel : Nat) (enough : statement.size < fuel) (rest : List Token) :
    parseRollbackStmt fuel (statement.tokens ++ rest) = some (statement, rest) := by
  cases statement with
  | storage statement =>
      have statementNames : statement.NamesOk := names
      have statementEnough : statement.size < fuel := enough
      simp only [RollbackStmt.tokens]
      simp [parseRollbackStmt, parseRevertIf_storage statement statementNames fuel statementEnough,
        parseLetOperation_storage statement statementNames fuel statementEnough,
        parseStorageStmt_tokens statement statementNames fuel statementEnough rest]
  | letOperation identifier type op left right =>
      have parsed := parseLetOperation_tokens identifier type op left right fuel rest names
        enough
      have notRevert : parseRevertIf fuel
          ((RollbackStmt.letOperation identifier type op left right).tokens ++ rest) = none := by
        simp [RollbackStmt.tokens, parseRevertIf, expectTokens]
      simp [parseRollbackStmt, notRevert, parsed]
  | revertIf op left right offset value dataOffset size =>
      have parsed := parseRevertIf_tokens op left right offset value dataOffset size fuel rest
        names enough
      simp [parseRollbackStmt, parsed]

theorem RollbackStmt.blockEnds_tokens (statement : RollbackStmt) (names : statement.NamesOk)
    (rest : List Token) : blockEnds (statement.tokens ++ rest) = false := by
  cases statement with
  | storage statement => exact StorageStmt.blockEnds_tokens statement names rest
  | letOperation => rfl
  | revertIf => rfl

theorem parseRollbackStmts_tokens : ∀ (statements : List RollbackStmt) (fuel : Nat)
    (rest : List Token), RollbackStmt.ListNamesOk statements →
    RollbackStmt.listSize statements < fuel → blockEnds rest = true →
    parseRollbackStmts fuel (RollbackStmt.listTokens statements ++ rest) =
      some (statements, rest)
  | [], fuel + 1, rest, _, _, ends => by
      simp [RollbackStmt.listTokens, parseRollbackStmts, ends]
  | statement :: more, fuel + 1, rest, names, enough, ends => by
      have statementNames : statement.NamesOk :=
        fun name mem => names name (by simp [RollbackStmt.listIdentifiers, mem])
      have moreNames : RollbackStmt.ListNamesOk more :=
        fun name mem => names name (by simp [RollbackStmt.listIdentifiers, mem])
      have statementParse := parseRollbackStmt_tokens statement statementNames fuel
        (by simp only [RollbackStmt.listSize] at enough; omega)
        (RollbackStmt.listTokens more ++ rest)
      have moreParse := parseRollbackStmts_tokens more fuel rest moreNames
        (by simp only [RollbackStmt.listSize] at enough; omega) ends
      simp only [RollbackStmt.listTokens, List.append_assoc]
      simp [parseRollbackStmts, RollbackStmt.blockEnds_tokens statement statementNames,
        statementParse, moreParse]

theorem parseRollbackImport_tokens (aliases : List (String × String)) (rest : List Token) :
    parseRollbackImport (rollbackImportTokens aliases ++ rest) = some (aliases, rest) := by
  cases aliases with
  | nil => simp [rollbackImportTokens, storageAliasTokens, parseRollbackImport, expectTokens]
  | cons alias more =>
      have length := aliasTokens_length (alias :: more)
      simp only [rollbackImportTokens, storageAliasTokens, List.append_assoc, List.cons_append,
        List.nil_append]
      simp [parseRollbackImport, expectTokens]
      rw [parseAliasList_tokens (alias :: more) _ _ (by simp) (by omega) rfl]
      simp [expectTokens]

theorem RollbackStmt.size_lt_tokens (statement : RollbackStmt) :
    statement.size < statement.tokens.length := by
  cases statement with
  | storage statement => exact StorageStmt.size_lt_tokens statement
  | letOperation identifier type op left right =>
      have := Expr.size_le_tokens left
      have := Expr.size_le_tokens right
      simp only [RollbackStmt.size, RollbackStmt.tokens, List.length_append, List.length_cons,
        List.length_nil]
      omega
  | revertIf op left right offset value dataOffset size =>
      have := Expr.size_le_tokens left
      have := Expr.size_le_tokens right
      have := Operand.size_le_tokens offset
      have := Operand.size_le_tokens value
      have := Operand.size_le_tokens dataOffset
      have := Operand.size_le_tokens size
      simp only [RollbackStmt.size, RollbackStmt.tokens, List.length_append, List.length_cons,
        List.length_nil]
      omega

theorem RollbackStmt.listSize_le_tokens : (statements : List RollbackStmt) →
    RollbackStmt.listSize statements ≤ (RollbackStmt.listTokens statements).length
  | [] => by simp [RollbackStmt.listSize, RollbackStmt.listTokens]
  | statement :: rest => by
      have := RollbackStmt.size_lt_tokens statement
      have := RollbackStmt.listSize_le_tokens rest
      simp only [RollbackStmt.listSize, RollbackStmt.listTokens, List.length_append]
      omega

theorem parseRollbackFileWith_tokens (file : RollbackFile) (names : file.NamesOk) (fuel : Nat)
    (functionsFuel : ∀ function ∈ file.functions,
      Stmt.listSize function.body < fuel ∧ function.result.size < fuel)
    (bodyFuel : RollbackStmt.listSize file.method.body < fuel)
    (resultFuel : file.method.result.size < fuel) :
    parseRollbackFileWith fuel file.tokens = some file := by
  obtain ⟨functionsOk, contractOk, methodOk, parametersOk, bodyOk, resultOk⟩ := names
  have resultParse := parseOperand_tokens file.method.result fuel (.symbol ')')
    [.symbol ';', .symbol '}', .symbol '}'] resultOk resultFuel (Or.inl rfl)
  have bodyParse := parseRollbackStmts_tokens file.method.body fuel
    (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
      [.symbol ')', .symbol ';', .symbol '}', .symbol '}'])) bodyOk bodyFuel rfl
  have parametersParse := parseParameters_tokens file.method.parameters
    (signatureTokens ++ (RollbackStmt.listTokens file.method.body ++
      (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
        [.symbol ')', .symbol ';', .symbol '}', .symbol '}'])))) parametersOk rfl
  have functionsLength := functions_length_le_tokens file.functions
  have functionsParse := parseFunctions_tokens file.functions (file.tokens.length + 1) fuel
    (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
      .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
        (signatureTokens ++ (RollbackStmt.listTokens file.method.body ++
          (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
            [.symbol ')', .symbol ';', .symbol '}', .symbol '}']))))))
    (fun function mem => ⟨functionsOk function mem, functionsFuel function mem⟩)
    (by simp only [RollbackFile.tokens, List.length_append] at functionsLength ⊢; omega)
    (by simp)
  have importParse := parseRollbackImport_tokens file.opcodeAliases
    (file.functions.flatMap FunctionDecl.tokens ++
      (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
        .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
          (signatureTokens ++ (RollbackStmt.listTokens file.method.body ++
            (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
              [.symbol ')', .symbol ';', .symbol '}', .symbol '}'])))))))
  unfold parseRollbackFileWith
  conv => lhs; arg 1; rw [RollbackFile.tokens]
  simp only [List.append_assoc, List.cons_append, List.nil_append, expectTokens_append,
    Option.bind_eq_bind, Option.bind_some]
  rw [importParse]
  simp only [Option.bind_some]
  rw [functionsParse]
  simp [expectTokens, parseName_cons contractOk, parseName_cons methodOk, parametersParse,
    expectTokens_append, bodyParse, resultParse]

/-- **Parser round trip.** Parsing the tokens of a rollback file with
non-reserved names returns that file. -/
theorem parseRollbackFile_tokens (file : RollbackFile) (names : file.NamesOk) :
    parseRollbackFile file.tokens = some file := by
  have bodySize := RollbackStmt.listSize_le_tokens file.method.body
  have resultSize := Operand.size_le_tokens file.method.result
  apply parseRollbackFileWith_tokens file names
  · intro function mem
    have := functions_sizes_le_tokens mem
    simp only [RollbackFile.tokens, List.length_append]
    omega
  · simp only [RollbackFile.tokens, List.length_append] at bodySize ⊢
    omega
  · simp only [RollbackFile.tokens, List.length_append, List.length_cons] at resultSize ⊢
    omega

/-! ### Printed pieces -/

def RollbackStmt.linePieces (indent : Nat) : RollbackStmt → List (List Piece)
  | .storage statement => statement.linePieces indent
  | .letOperation identifier type op left right =>
      [blanks indent ++ [word "let", space, word identifier, sym ':', space] ++ type.pieces ++
        [space, sym '=', space] ++ (Operand.operation op left right).pieces ++ [sym ';']]
  | .revertIf op left right offset value dataOffset size =>
      [blanks indent ++ [word "if", space, sym '('] ++ (Operand.operation op left right).pieces ++
          [sym ')', space, sym '{'],
        blanks (indent + 4) ++ [word "mstore", sym '('] ++ offset.pieces ++ [sym ',', space] ++
          value.pieces ++ [sym ')', sym ';'],
        blanks (indent + 4) ++ [word "revert_", sym '('] ++ dataOffset.pieces ++
          [sym ',', space] ++ size.pieces ++ [sym ')', sym ';'],
        blanks indent ++ [sym '}']]

def RollbackStmt.listLinePieces (indent : Nat) : List RollbackStmt → List (List Piece)
  | [] => []
  | statement :: rest => statement.linePieces indent ++ RollbackStmt.listLinePieces indent rest

theorem RollbackStmt.lines_toList (indent : Nat) : (statement : RollbackStmt) →
    (statement.lines indent).map String.toList = (statement.linePieces indent).map render
  | .storage statement => StorageStmt.lines_toList indent statement
  | .letOperation identifier type op left right => by
      simp [RollbackStmt.lines, RollbackStmt.linePieces, indentLine_toList, render_append,
        render_blanks, render, Piece.chars, Token.chars, word, sym, space,
        LocalType.spelling_toList, Operand.print_toList]
  | .revertIf op left right offset value dataOffset size => by
      simp [RollbackStmt.lines, RollbackStmt.linePieces, indentLine_toList, render_append,
        render_blanks, render, Piece.chars, Token.chars, word, sym, space, Operand.print_toList]

theorem RollbackStmt.listLines_toList (indent : Nat) : (statements : List RollbackStmt) →
    (RollbackStmt.listLines indent statements).map String.toList =
      (RollbackStmt.listLinePieces indent statements).map render
  | [] => rfl
  | statement :: rest => by
      simp [RollbackStmt.listLines, RollbackStmt.listLinePieces,
        RollbackStmt.lines_toList indent statement, RollbackStmt.listLines_toList indent rest]

theorem RollbackStmt.linePieces_tokens (indent : Nat) : (statement : RollbackStmt) →
    ((statement.linePieces indent).map tokensOf).flatten = statement.tokens
  | .storage statement => StorageStmt.linePieces_tokens indent statement
  | .letOperation identifier type op left right => by
      simp [RollbackStmt.linePieces, RollbackStmt.tokens, tokensOf_append, tokensOf_blanks,
        tokensOf, word, sym, space, LocalType.tokensOf_pieces, Operand.tokensOf_pieces,
        Operand.tokens]
  | .revertIf op left right offset value dataOffset size => by
      simp [RollbackStmt.linePieces, RollbackStmt.tokens, tokensOf_append, tokensOf_blanks,
        tokensOf, word, sym, space, Operand.tokensOf_pieces, Operand.tokens]

theorem RollbackStmt.listLinePieces_tokens (indent : Nat) : (statements : List RollbackStmt) →
    ((RollbackStmt.listLinePieces indent statements).map tokensOf).flatten =
      RollbackStmt.listTokens statements
  | [] => rfl
  | statement :: rest => by
      simp [RollbackStmt.listLinePieces, RollbackStmt.listTokens,
        RollbackStmt.linePieces_tokens indent statement,
        RollbackStmt.listLinePieces_tokens indent rest]

/-- `call(a, b);` at an indentation, for valid operands, is separated. -/
theorem callPieces_separated (indent : Nat) (callee : String) (calleeValid : ValidIdentifier callee)
    (first second : Operand) (firstValid : ∀ name ∈ first.identifiers, ValidIdentifier name)
    (secondValid : ∀ name ∈ second.identifiers, ValidIdentifier name) :
    Separated (blanks indent ++ [word callee, sym '('] ++ first.pieces ++ [sym ',', space] ++
      second.pieces ++ [sym ')', sym ';']) := by
  have secondPart := Operand.separated_append second secondValid [sym ')', sym ';']
    (Separated.cons_sym (by decide) (sym_valid (by decide))) (head_sym (by decide))
  have firstPart := Operand.separated_append first firstValid
    (sym ',' :: space :: (second.pieces ++ [sym ')', sym ';']))
    (Separated.cons_sym (by decide) (Separated.cons_space secondPart)) (head_sym (by decide))
  simp only [List.append_assoc, List.cons_append, List.nil_append] at firstPart ⊢
  exact Separated.blanks_append indent (Separated.cons_word calleeValid
    (Separated.cons_sym (by decide) firstPart) (head_sym (by decide)))

theorem RollbackStmt.linePieces_separated (indent : Nat) : (statement : RollbackStmt) →
    (∀ name ∈ statement.identifiers, ValidIdentifier name) →
    ∀ line ∈ statement.linePieces indent, Separated line
  | .storage statement, valid, line, mem =>
      StorageStmt.linePieces_separated indent statement valid line mem
  | .letOperation identifier type op left right, valid, line, mem => by
      simp only [RollbackStmt.linePieces, List.mem_singleton] at mem
      subst mem
      have operation := Operand.separated_append (.operation op left right)
        (fun name mem => valid name (List.mem_cons_of_mem _ mem))
        [sym ';'] (sym_valid (by decide)) (head_sym (by decide))
      have typePart := LocalType.separated_append type _ (Separated.cons_space
        (Separated.cons_equal (Separated.cons_space operation) (fun next same => by
          cases same; rfl))) head_space
      simp only [List.append_assoc, List.cons_append, List.nil_append] at typePart ⊢
      exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
        (Separated.cons_space (Separated.cons_word
          (valid identifier (by simp [RollbackStmt.identifiers]))
          (Separated.cons_sym (by decide) (Separated.cons_space typePart))
          (head_sym (by decide))))
        head_space)
  | .revertIf op left right offset value dataOffset size, valid, line, mem => by
      have within : ∀ name, name ∈ left.identifiers ∨ name ∈ right.identifiers ∨
          name ∈ offset.identifiers ∨ name ∈ value.identifiers ∨
          name ∈ dataOffset.identifiers ∨ name ∈ size.identifiers → ValidIdentifier name := by
        intro name found
        apply valid name
        simp only [RollbackStmt.identifiers, List.mem_append]
        rcases found with found | found | found | found | found | found <;> simp [found]
      simp only [RollbackStmt.linePieces, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with same | same | same | same
      · subst same
        have operation := Operand.separated_append (.operation op left right)
          (fun name found => by
            simp only [Operand.identifiers, List.mem_append] at found
            rcases found with found | found
            · exact within name (Or.inl found)
            · exact within name (Or.inr (Or.inl found)))
          [sym ')', space, sym '{'] (Separated.cons_sym (by decide) (Separated.cons_space
            (sym_valid (by decide)))) (head_sym (by decide))
        simp only [List.append_assoc, List.cons_append, List.nil_append] at operation ⊢
        exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_space (Separated.cons_sym (by decide) operation)) head_space)
      · subst same
        exact callPieces_separated (indent + 4) "mstore" (keyword_valid (by decide)) offset value
          (fun name found => within name (Or.inr (Or.inr (Or.inl found))))
          (fun name found => within name (Or.inr (Or.inr (Or.inr (Or.inl found)))))
      · subst same
        exact callPieces_separated (indent + 4) "revert_" (keyword_valid (by decide)) dataOffset
          size (fun name found => within name (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl found))))))
          (fun name found => within name (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr found))))))
      · subst same
        exact Separated.blanks_append indent (sym_valid (by decide))

theorem RollbackStmt.listLinePieces_separated (indent : Nat) :
    (statements : List RollbackStmt) →
    (∀ name ∈ RollbackStmt.listIdentifiers statements, ValidIdentifier name) →
    ∀ line ∈ RollbackStmt.listLinePieces indent statements, Separated line
  | [], _, _, mem => by simp [RollbackStmt.listLinePieces] at mem
  | statement :: rest, valid, line, mem => by
      simp only [RollbackStmt.listLinePieces, List.mem_append] at mem
      rcases mem with mem | mem
      · exact RollbackStmt.linePieces_separated indent statement
          (fun name found => valid name (by simp [RollbackStmt.listIdentifiers, found])) line mem
      · exact RollbackStmt.listLinePieces_separated indent rest
          (fun name found => valid name (by simp [RollbackStmt.listIdentifiers, found])) line mem

def rollbackImportPieces (aliases : List (String × String)) : List Piece :=
  [word "import", space, sym '{', word "sload", sym ',', space, word "sstore", sym ',', space,
    word "mstore", sym ',', space, word "revert_"] ++ storageAliasPieces aliases ++
    [sym '}', space, word "from", space, word "std", sym '.', word "opcodes", sym ';']

theorem rollbackImportLine_toList (aliases : List (String × String)) :
    (rollbackImportLine aliases).toList = render (rollbackImportPieces aliases) := by
  cases aliases with
  | nil =>
      simp [rollbackImportLine, rollbackImportPieces, storageAliasPieces,
        String.intercalate_cons_cons, render, Piece.chars, Token.chars, word, sym, space]
  | cons alias more =>
      have tail := aliasText_toList (alias :: more)
      simp only [List.map_cons] at tail
      simp only [rollbackImportLine, List.cons_append, List.nil_append, List.map_cons]
      rw [String.intercalate_cons_cons, String.intercalate_cons_cons,
        String.intercalate_cons_cons, String.intercalate_cons_cons]
      simp only [String.toList_append, tail]
      simp [rollbackImportPieces, storageAliasPieces, render_append, render, Piece.chars,
        Token.chars, word, sym, space]

theorem rollbackImportPieces_tokens (aliases : List (String × String)) :
    tokensOf (rollbackImportPieces aliases) = rollbackImportTokens aliases := by
  cases aliases <;>
    simp [rollbackImportPieces, storageAliasPieces, rollbackImportTokens, storageAliasTokens,
      tokensOf_append, tokensOf, word, sym, space, aliasPieces_tokens]

theorem rollbackImportPieces_separated (aliases : List (String × String))
    (valid : ∀ alias ∈ aliases, ValidIdentifier alias.1 ∧ ValidIdentifier alias.2) :
    Separated (rollbackImportPieces aliases) := by
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
  simp only [rollbackImportPieces, List.cons_append, List.nil_append]
  exact Separated.cons_word (keyword_valid (by decide)) (Separated.cons_space
    (Separated.cons_sym (by decide) (Separated.cons_word (keyword_valid (by decide))
      (Separated.cons_sym (by decide) (Separated.cons_space (Separated.cons_word
        (keyword_valid (by decide)) (Separated.cons_sym (by decide) (Separated.cons_space
          (Separated.cons_word (keyword_valid (by decide)) (Separated.cons_sym (by decide)
            (Separated.cons_space (Separated.cons_word (keyword_valid (by decide)) middle.1
              middle.2))) (head_sym (by decide))))) (head_sym (by decide)))))
      (head_sym (by decide))))) head_space

def RollbackFile.linePieces (file : RollbackFile) : List (List Piece) :=
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
  RollbackStmt.listLinePieces 8 file.method.body ++
  [blanks 8 ++ [word "return", space, word "uint256", sym '('] ++ file.method.result.pieces ++
      [sym ')', sym ';'],
    blanks 4 ++ [sym '}'], [sym '}']]

theorem RollbackFile.lines_toList (file : RollbackFile) :
    file.lines.map String.toList = file.linePieces.map render := by
  simp only [RollbackFile.lines, RollbackFile.linePieces, List.map_append, functions_lines_toList]
  simp [RollbackStmt.listLines_toList, parameterText_toList, Operand.print_toList,
    rollbackImportLine_toList, render_append, render_blanks, render, Piece.chars, Token.chars,
    word, sym, space]

theorem RollbackFile.linePieces_tokens (file : RollbackFile) :
    (file.linePieces.map tokensOf).flatten = file.tokens := by
  simp only [RollbackFile.linePieces, RollbackFile.tokens, List.map_append, List.flatten_append,
    functions_linePieces_tokens]
  simp [importTokens, signatureTokens, RollbackStmt.listLinePieces_tokens,
    parameterPieces_tokens, Operand.tokensOf_pieces, rollbackImportPieces_tokens,
    tokensOf_append, tokensOf_blanks, tokensOf, word, sym, space]

/-- Every identifier of the rollback file is lexically valid. -/
def RollbackFile.IdentifiersValid (file : RollbackFile) : Prop :=
  (∀ alias ∈ file.opcodeAliases, ValidIdentifier alias.1 ∧ ValidIdentifier alias.2) ∧
    (∀ function ∈ file.functions, ∀ name ∈ function.identifiers, ValidIdentifier name) ∧
    ValidIdentifier file.contract ∧ ValidIdentifier file.method.name ∧
    (∀ parameter ∈ file.method.parameters, ValidIdentifier parameter) ∧
    (∀ name ∈ RollbackStmt.listIdentifiers file.method.body, ValidIdentifier name) ∧
    (∀ name ∈ file.method.result.identifiers, ValidIdentifier name)

/-- The rollback file without aliases, method body or returned operand. Its
lines are the rollback file's import, function, contract and closing lines. -/
def RollbackFile.skeleton (file : RollbackFile) : SourceFile where
  opcodeAliases := []
  functions := file.functions
  contract := file.contract
  method := {
    name := file.method.name, parameters := file.method.parameters, body := [],
    result := .number 0 }

theorem RollbackFile.linePieces_separated (file : RollbackFile)
    (valid : file.IdentifiersValid) : ∀ line ∈ file.linePieces, Separated line := by
  obtain ⟨aliasesValid, functionsValid, contractValid, methodValid, parametersValid, bodyValid,
    resultValid⟩ := valid
  have skeleton := file.skeleton.linePieces_separated ⟨by simp [RollbackFile.skeleton],
    functionsValid, contractValid, methodValid, parametersValid,
    by simp [RollbackFile.skeleton, Stmt.listIdentifiers],
    by simp [RollbackFile.skeleton, Expr.identifiers]⟩
  intro line mem
  unfold RollbackFile.linePieces at mem
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
    · exact RollbackStmt.listLinePieces_separated 8 file.method.body bodyValid line mem
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

theorem RollbackFile.print_toList (file : RollbackFile) :
    file.print.toList = render (joinLines file.linePieces) := by
  rw [RollbackFile.print, String.toList_append, String.toList_intercalate, joinLines,
    render_append, render_intercalate, RollbackFile.lines_toList]
  rfl

/-- **Text round trip.** The printed text of a rollback file with lexically
valid, non-reserved names parses back to that file. -/
theorem parseRollbackSource_print (file : RollbackFile) (names : file.NamesOk)
    (valid : file.IdentifiersValid) : parseRollbackSource file.print = some file := by
  rw [parseRollbackSource, RollbackFile.print_toList,
    lex_render (joinLines_separated _ (file.linePieces_separated valid)), Option.bind_some,
    tokensOf_joinLines, RollbackFile.linePieces_tokens]
  exact parseRollbackFile_tokens file names

/-- The meaning of a printed rollback file's text is the meaning of the file. -/
theorem rollbackSourceCall_print (file : RollbackFile) (names : file.NamesOk)
    (valid : file.IdentifiersValid) (storage : Storage) (method : String)
    (arguments : List Nat) :
    rollbackSourceCall file.print storage method arguments =
      file.call storage method arguments := by
  simp [rollbackSourceCall, parseRollbackSource_print file names valid]

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.KeyedText
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
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.LogText
/-! Text of log programs. `parseLogSource` lexes a complete text as
`parseSource` does and parses it with the rollback grammar, extended by the log
import line, stores and log blocks. Each extension is recognized from its first
tokens: a store starts with `mstore (`, which no rollback statement starts with,
and a log block goes on with an infix operator after the first expression of its
condition and with `let` after its brace, where a loop-free `if` condition ends
with `)` and the revert block goes on with `mstore`. Inside a log block, stores
are read while the next tokens are `mstore (`, so a logger named `mstore` would
read as a store. The printed text of every log file with valid, non-reserved
names and no logger named `mstore` parses back to that file. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

/-! ### Tokens -/

def storeTokens (offset value : Operand) : List Token :=
  [.ident "mstore", .symbol '('] ++ offset.tokens ++ [.symbol ','] ++ value.tokens ++
    [.symbol ')', .symbol ';']

def storesTokens : List (Operand × Operand) → List Token
  | [] => []
  | (offset, value) :: rest => storeTokens offset value ++ storesTokens rest

/-- Each topic after a comma. -/
def topicsTokens : List Operand → List Token
  | [] => []
  | topic :: rest => .symbol ',' :: (topic.tokens ++ topicsTokens rest)

def LogBlock.tokens (block : LogBlock) : List Token :=
  block.binding.tokens ++ storesTokens block.stores ++ [.ident block.logger, .symbol '('] ++
    block.dataOffset.tokens ++ [.symbol ','] ++ block.dataSize.tokens ++
    topicsTokens block.topics ++ [.symbol ')', .symbol ';']

def LogStmt.tokens : LogStmt → List Token
  | .rollback statement => statement.tokens
  | .store offset value => storeTokens offset value
  | .logIf op left right block =>
      [.ident "if", .symbol '('] ++ left.tokens ++ [op.token] ++ right.tokens ++
        [.symbol ')', .symbol '{'] ++ block.tokens ++ [.symbol '}']

def LogStmt.listTokens : List LogStmt → List Token
  | [] => []
  | statement :: rest => statement.tokens ++ LogStmt.listTokens rest

def logImportTokens (aliases : List (String × String)) : List Token :=
  [.ident "import", .symbol '{', .ident "sload", .symbol ',', .ident "sstore", .symbol ',',
    .ident "mload", .symbol ',', .ident "mstore", .symbol ',', .ident "revert_"] ++
    storageAliasTokens aliases ++
    [.symbol '}', .ident "from", .ident "std", .symbol '.', .ident "opcodes", .symbol ';']

def LogFile.tokens (file : LogFile) : List Token :=
  importTokens ++ logImportTokens file.opcodeAliases ++
    file.functions.flatMap FunctionDecl.tokens ++
    [.ident "contract", .ident file.contract, .symbol '{', .ident "function",
      .ident file.method.name, .symbol '('] ++ parameterTokens file.method.parameters ++
    signatureTokens ++ LogStmt.listTokens file.method.body ++
    [.ident "return", .ident "uint256", .symbol '('] ++ file.method.result.tokens ++
    [.symbol ')', .symbol ';', .symbol '}', .symbol '}']

/-! ### Parser -/

/-- `mstore(offset, value);` -/
def parseStore (fuel : Nat) (tokens : List Token) :
    Option ((Operand × Operand) × List Token) := do
  let rest ← expectTokens [.ident "mstore", .symbol '('] tokens
  let (offset, rest) ← parseOperand fuel rest
  let rest ← expectTokens [.symbol ','] rest
  let (value, rest) ← parseOperand fuel rest
  let rest ← expectTokens [.symbol ')', .symbol ';'] rest
  some ((offset, value), rest)

/-- Stores, while the next tokens are `mstore (`. -/
def parseStores : Nat → List Token → Option (List (Operand × Operand) × List Token)
  | 0, _ => none
  | fuel + 1, tokens =>
      if tokens.take 2 = [.ident "mstore", .symbol '('] then do
        let (store, rest) ← parseStore fuel tokens
        let (stores, rest) ← parseStores fuel rest
        some (store :: stores, rest)
      else some ([], tokens)

/-- Topics, each after a comma. -/
def parseTopics : Nat → List Token → Option (List Operand × List Token)
  | 0, _ => none
  | fuel + 1, tokens =>
      match tokens with
      | .symbol ',' :: rest => do
          let (topic, rest) ← parseOperand fuel rest
          let (topics, rest) ← parseTopics fuel rest
          some (topic :: topics, rest)
      | _ => some ([], tokens)

/-- The log block, when an infix operator follows the first expression of its
condition and a call `let` opens its braces. -/
def parseLogIf (fuel : Nat) (tokens : List Token) : Option (LogStmt × List Token) := do
  let rest ← expectTokens [.ident "if", .symbol '('] tokens
  let (left, rest) ← parseExpr fuel rest
  match rest with
  | next :: rest => do
      let op ← parseBinaryOp? next
      let (right, rest) ← parseExpr fuel rest
      let rest ← expectTokens [.symbol ')', .symbol '{'] rest
      let (binding, rest) ← parseLetCall fuel rest
      match binding with
      | .letCall identifier type callee bindOp bindLeft bindRight => do
          let (stores, rest) ← parseStores fuel rest
          let (logger, rest) ← parseName rest
          let rest ← expectTokens [.symbol '('] rest
          let (dataOffset, rest) ← parseOperand fuel rest
          let rest ← expectTokens [.symbol ','] rest
          let (dataSize, rest) ← parseOperand fuel rest
          let (topics, rest) ← parseTopics fuel rest
          let rest ← expectTokens [.symbol ')', .symbol ';', .symbol '}'] rest
          some (.logIf op left right ⟨identifier, type, callee, bindOp, bindLeft, bindRight,
            stores, logger, dataOffset, dataSize, topics⟩, rest)
      | _ => none
  | [] => none

/-- A log block, a store, or otherwise a rollback statement. -/
def parseLogStmt (fuel : Nat) (tokens : List Token) : Option (LogStmt × List Token) :=
  match parseLogIf fuel tokens with
  | some parsed => some parsed
  | none =>
      match parseStore fuel tokens with
      | some (store, rest) => some (.store store.1 store.2, rest)
      | none => (parseRollbackStmt fuel tokens).map fun parsed => (.rollback parsed.1, parsed.2)

def parseLogStmts : Nat → List Token → Option (List LogStmt × List Token)
  | 0, _ => none
  | fuel + 1, tokens =>
      if blockEnds tokens then some ([], tokens)
      else do
        let (statement, rest) ← parseLogStmt fuel tokens
        let (statements, rest) ← parseLogStmts fuel rest
        some (statement :: statements, rest)

/-- `import {sload, sstore, mload, mstore, revert_, opcode as alias, ...} from std.opcodes;` -/
def parseLogImport (tokens : List Token) : Option (List (String × String) × List Token) := do
  let rest ← expectTokens
    [.ident "import", .symbol '{', .ident "sload", .symbol ',', .ident "sstore", .symbol ',',
      .ident "mload", .symbol ',', .ident "mstore", .symbol ',', .ident "revert_"] tokens
  let (aliases, rest) ←
    if rest.head? = some (.symbol ',') then parseAliasList rest.length rest.tail
    else some ([], rest)
  let rest ← expectTokens
    [.symbol '}', .ident "from", .ident "std", .symbol '.', .ident "opcodes", .symbol ';'] rest
  some (aliases, rest)

/-- `parseRollbackFileWith` with the log import line and a log method body. -/
def parseLogFileWith (fuel : Nat) (tokens : List Token) : Option LogFile := do
  let rest ← expectTokens importTokens tokens
  let (opcodeAliases, rest) ← parseLogImport rest
  let (functions, rest) ← parseFunctions (tokens.length + 1) fuel rest
  let rest ← expectTokens [.ident "contract"] rest
  let (contract, rest) ← parseName rest
  let rest ← expectTokens [.symbol '{', .ident "function"] rest
  let (method, rest) ← parseName rest
  let rest ← expectTokens [.symbol '('] rest
  let (parameters, rest) ← parseParameters rest
  let rest ← expectTokens signatureTokens rest
  let (body, rest) ← parseLogStmts fuel rest
  let rest ← expectTokens [.ident "return", .ident "uint256", .symbol '('] rest
  let (result, rest) ← parseOperand fuel rest
  let rest ← expectTokens [.symbol ')', .symbol ';', .symbol '}', .symbol '}'] rest
  if rest = [] then
    some ⟨opcodeAliases, functions, contract, ⟨method, parameters, body, result⟩⟩
  else none

/-- Parse a complete token stream; one more than its length bounds nesting. -/
def parseLogFile (tokens : List Token) : Option LogFile :=
  parseLogFileWith (tokens.length + 1) tokens

def parseLogSource (source : String) : Option LogFile :=
  (lex source.toList).bind parseLogFile

/-- The outcome of calling `method` from `storage` and `memory` on the contract
written in `source`, read as a log program. -/
def logSourceCall (source : String) (storage : Storage) (memory : Memory) (method : String)
    (arguments : List Nat) : Option LogOutcome :=
  (parseLogSource source).bind fun file => file.call storage memory method arguments

/-! ### Sizes and names -/

def storesSize : List (Operand × Operand) → Nat
  | [] => 0
  | (offset, value) :: rest => offset.size + value.size + storesSize rest + 1

def topicsSize : List Operand → Nat
  | [] => 0
  | topic :: rest => topic.size + topicsSize rest + 1

def LogBlock.size (block : LogBlock) : Nat :=
  block.binding.size + storesSize block.stores + block.dataOffset.size + block.dataSize.size +
    topicsSize block.topics

def LogStmt.size : LogStmt → Nat
  | .rollback statement => statement.size
  | .store offset value => offset.size + value.size
  | .logIf _ left right block => left.size + right.size + block.size

def LogStmt.listSize : List LogStmt → Nat
  | [] => 0
  | statement :: rest => statement.size + LogStmt.listSize rest + 1

def LogStmt.NamesOk (statement : LogStmt) : Prop :=
  ∀ name ∈ statement.identifiers, isReserved name = false

def LogStmt.ListNamesOk (statements : List LogStmt) : Prop :=
  ∀ name ∈ LogStmt.listIdentifiers statements, isReserved name = false

/-- A log block's logger is not `mstore`. -/
def LogStmt.LoggerOk : LogStmt → Prop
  | .logIf _ _ _ block => block.logger ≠ "mstore"
  | _ => True

def LogFile.NamesOk (file : LogFile) : Prop :=
  (∀ function ∈ file.functions, function.NamesOk) ∧
    isReserved file.contract = false ∧ isReserved file.method.name = false ∧
    (∀ parameter ∈ file.method.parameters, isReserved parameter = false) ∧
    LogStmt.ListNamesOk file.method.body ∧
    (∀ statement ∈ file.method.body, statement.LoggerOk) ∧ file.method.result.NamesOk

/-! ### Round trip -/

theorem parseStores_tokens : ∀ (stores : List (Operand × Operand)) (fuel : Nat)
    (rest : List Token), (∀ name ∈ storesIdentifiers stores, isReserved name = false) →
    storesSize stores < fuel → rest.take 2 ≠ [.ident "mstore", .symbol '('] →
    parseStores fuel (storesTokens stores ++ rest) = some (stores, rest)
  | [], fuel + 1, rest, _, _, notStore => by simp [storesTokens, parseStores, notStore]
  | (offset, value) :: more, fuel + 1, rest, names, enough, notStore => by
      have offsetParse := parseOperand_tokens offset fuel (.symbol ',')
        (value.tokens ++ .symbol ')' :: .symbol ';' :: (storesTokens more ++ rest))
        (fun name mem => names name (by simp [storesIdentifiers, mem]))
        (by simp only [storesSize] at enough; omega) (Or.inr rfl)
      have valueParse := parseOperand_tokens value fuel (.symbol ')')
        (.symbol ';' :: (storesTokens more ++ rest))
        (fun name mem => names name (by simp [storesIdentifiers, mem]))
        (by simp only [storesSize] at enough; omega) (Or.inl rfl)
      have moreParse := parseStores_tokens more fuel rest
        (fun name mem => names name (by simp [storesIdentifiers, mem]))
        (by simp only [storesSize] at enough; omega) notStore
      simp only [storesTokens, storeTokens, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseStores, parseStore, expectTokens, offsetParse, valueParse, moreParse]

theorem parseTopics_tokens : ∀ (topics : List Operand) (fuel : Nat) (after : List Token),
    (∀ name ∈ topicsIdentifiers topics, isReserved name = false) →
    topicsSize topics < fuel →
    parseTopics fuel (topicsTokens topics ++ .symbol ')' :: after) =
      some (topics, .symbol ')' :: after)
  | [], fuel + 1, after, _, _ => by simp [topicsTokens, parseTopics]
  | topic :: more, fuel + 1, after, names, enough => by
      have moreParse := parseTopics_tokens more fuel after
        (fun name mem => names name (by simp [topicsIdentifiers, mem]))
        (by simp only [topicsSize] at enough; omega)
      obtain ⟨close, following, split, closing⟩ : ∃ close following,
          topicsTokens more ++ .symbol ')' :: after = close :: following ∧
            (close = .symbol ')' ∨ close = .symbol ',') := by
        cases more with
        | nil => exact ⟨_, _, rfl, Or.inl rfl⟩
        | cons => exact ⟨_, _, rfl, Or.inr rfl⟩
      have topicParse := parseOperand_tokens topic fuel close following
        (fun name mem => names name (by simp [topicsIdentifiers, mem]))
        (by simp only [topicsSize] at enough; omega) closing
      rw [split] at moreParse
      simp only [topicsTokens, List.cons_append, List.append_assoc]
      rw [split]
      simp [parseTopics, topicParse, moreParse]

/-- The tokens after a log's size: its topics, then `)`. -/
theorem topicsTokens_close (topics : List Operand) (after : List Token) :
    ∃ close following, topicsTokens topics ++ .symbol ')' :: after = close :: following ∧
      (close = .symbol ')' ∨ close = .symbol ',') := by
  cases topics with
  | nil => exact ⟨_, _, rfl, Or.inl rfl⟩
  | cons => exact ⟨_, _, rfl, Or.inr rfl⟩

theorem parseLogIf_tokens (op : BinaryOp) (left right : Expr) (block : LogBlock) (fuel : Nat)
    (rest : List Token) (names : (LogStmt.logIf op left right block).NamesOk)
    (logger : block.logger ≠ "mstore")
    (enough : (LogStmt.logIf op left right block).size < fuel) :
    parseLogIf fuel ((LogStmt.logIf op left right block).tokens ++ rest) =
      some (.logIf op left right block, rest) := by
  have within : ∀ name ∈ block.identifiers, isReserved name = false :=
    fun name mem => names name (by simp [LogStmt.identifiers, mem])
  have sizes : left.size + right.size + block.binding.size + storesSize block.stores +
      block.dataOffset.size + block.dataSize.size + topicsSize block.topics < fuel := by
    simp only [LogStmt.size, LogBlock.size] at enough
    omega
  have loggerOk : isReserved block.logger = false :=
    within block.logger (by simp [LogBlock.identifiers])
  obtain ⟨close, following, split, closing⟩ :=
    topicsTokens_close block.topics (.symbol ';' :: .symbol '}' :: rest)
  have topicsParse := parseTopics_tokens block.topics fuel (.symbol ';' :: .symbol '}' :: rest)
    (fun name mem => within name (by simp [LogBlock.identifiers, mem])) (by omega)
  have sizeParse := parseOperand_tokens block.dataSize fuel close following
    (fun name mem => within name (by simp [LogBlock.identifiers, mem])) (by omega) closing
  rw [← split] at sizeParse
  have offsetParse := parseOperand_tokens block.dataOffset fuel (.symbol ',')
    (block.dataSize.tokens ++ (topicsTokens block.topics ++
      .symbol ')' :: .symbol ';' :: .symbol '}' :: rest))
    (fun name mem => within name (by simp [LogBlock.identifiers, mem])) (by omega) (Or.inr rfl)
  have storesParse := parseStores_tokens block.stores fuel
    (.ident block.logger :: .symbol '(' :: (block.dataOffset.tokens ++ .symbol ',' ::
      (block.dataSize.tokens ++ (topicsTokens block.topics ++
        .symbol ')' :: .symbol ';' :: .symbol '}' :: rest))))
    (fun name mem => within name (by simp [LogBlock.identifiers, mem])) (by omega)
    (by simp [logger])
  have bindingParse := parseLetCall_tokens block.identifier block.type block.callee block.op
    block.left block.right fuel
    (storesTokens block.stores ++ .ident block.logger :: .symbol '(' ::
      (block.dataOffset.tokens ++ .symbol ',' :: (block.dataSize.tokens ++
        (topicsTokens block.topics ++ .symbol ')' :: .symbol ';' :: .symbol '}' :: rest))))
    (fun name mem => within name (by simp [LogBlock.identifiers, LogBlock.binding, mem]))
    (by simp only [LogBlock.binding] at sizes; omega)
  have leftParse := parseExpr_tokens left fuel (op.token :: (right.tokens ++ .symbol ')' ::
      .symbol '{' :: (block.tokens ++ .symbol '}' :: rest)))
    (fun name mem => names name (by simp [LogStmt.identifiers, mem])) (by omega)
    (by simpa using BinaryOp.token_ne_open op)
  have rightParse := parseExpr_tokens right fuel (.symbol ')' :: .symbol '{' ::
      (block.tokens ++ .symbol '}' :: rest))
    (fun name mem => names name (by simp [LogStmt.identifiers, mem])) (by omega) (by simp)
  simp only [LogStmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
  simp only [LogBlock.tokens, LogBlock.binding, List.append_assoc, List.cons_append,
    List.nil_append] at leftParse rightParse ⊢
  simp [parseLogIf, expectTokens, leftParse, BinaryOp.parse_token, rightParse, bindingParse,
    storesParse, parseName_cons loggerOk, offsetParse, sizeParse, topicsParse]

theorem parseStore_tokens (offset value : Operand) (fuel : Nat) (rest : List Token)
    (names : (LogStmt.store offset value).NamesOk)
    (enough : (LogStmt.store offset value).size < fuel) :
    parseStore fuel (storeTokens offset value ++ rest) = some ((offset, value), rest) := by
  have offsetParse := parseOperand_tokens offset fuel (.symbol ',')
    (value.tokens ++ .symbol ')' :: .symbol ';' :: rest)
    (fun name mem => names name (by simp [LogStmt.identifiers, mem]))
    (by simp only [LogStmt.size] at enough; omega) (Or.inr rfl)
  have valueParse := parseOperand_tokens value fuel (.symbol ')') (.symbol ';' :: rest)
    (fun name mem => names name (by simp [LogStmt.identifiers, mem]))
    (by simp only [LogStmt.size] at enough; omega) (Or.inl rfl)
  simp only [storeTokens, List.append_assoc, List.cons_append, List.nil_append]
  simp [parseStore, expectTokens, offsetParse, valueParse]

/-- No rollback statement reads as a log block. -/
theorem parseLogIf_rollback (statement : RollbackStmt) (names : statement.NamesOk)
    (fuel : Nat) (enough : statement.size < fuel) (rest : List Token) :
    parseLogIf fuel (statement.tokens ++ rest) = none := by
  cases statement with
  | storage statement =>
      cases statement with
      | plain statement =>
          cases statement with
          | ifElse condition thenBlock elseBlock =>
              have conditionParse := parseExpr_tokens condition fuel
                (.symbol ')' :: .symbol '{' :: (Stmt.listTokens thenBlock ++
                  .symbol '}' :: .ident "else" :: .symbol '{' :: (Stmt.listTokens elseBlock ++
                    .symbol '}' :: rest)))
                (fun name mem => names name (by
                  simp [RollbackStmt.identifiers, StorageStmt.identifiers, Stmt.identifiers, mem]))
                (by simp only [RollbackStmt.size, StorageStmt.size, Stmt.size] at enough; omega)
                (by simp)
              simp only [RollbackStmt.tokens, StorageStmt.tokens, Stmt.tokens, List.append_assoc,
                List.cons_append, List.nil_append]
              simp [parseLogIf, expectTokens, conditionParse, parseBinaryOp?_close]
          | letDecl =>
              simp [RollbackStmt.tokens, StorageStmt.tokens, Stmt.tokens, parseLogIf,
                expectTokens]
          | assign identifier value =>
              have identifierOk : isReserved identifier = false :=
                names identifier (by
                  simp [RollbackStmt.identifiers, StorageStmt.identifiers, Stmt.identifiers])
              have notIf : "if" ≠ identifier :=
                fun same => (not_reserved_ne identifierOk).2.1 same.symm
              simp [RollbackStmt.tokens, StorageStmt.tokens, Stmt.tokens, parseLogIf,
                expectTokens, notIf]
          | matchPair =>
              simp [RollbackStmt.tokens, StorageStmt.tokens, Stmt.tokens, parseLogIf,
                expectTokens]
          | matchSum =>
              simp [RollbackStmt.tokens, StorageStmt.tokens, Stmt.tokens, parseLogIf,
                expectTokens]
      | letCall => simp [RollbackStmt.tokens, StorageStmt.tokens, parseLogIf, expectTokens]
      | store => simp [RollbackStmt.tokens, StorageStmt.tokens, parseLogIf, expectTokens]
  | letOperation => simp [RollbackStmt.tokens, parseLogIf, expectTokens]
  | revertIf op left right offset value dataOffset size =>
      have leftParse := parseExpr_tokens left fuel (op.token :: (right.tokens ++ .symbol ')' ::
          .symbol '{' :: .ident "mstore" :: .symbol '(' :: (offset.tokens ++ .symbol ',' ::
            (value.tokens ++ .symbol ')' :: .symbol ';' :: .ident "revert_" :: .symbol '(' ::
              (dataOffset.tokens ++ .symbol ',' :: (size.tokens ++
                .symbol ')' :: .symbol ';' :: .symbol '}' :: rest))))))
        (fun name mem => names name (by simp [RollbackStmt.identifiers, mem]))
        (by simp only [RollbackStmt.size] at enough; omega)
        (by simpa using BinaryOp.token_ne_open op)
      have rightParse := parseExpr_tokens right fuel (.symbol ')' ::
          .symbol '{' :: .ident "mstore" :: .symbol '(' :: (offset.tokens ++ .symbol ',' ::
            (value.tokens ++ .symbol ')' :: .symbol ';' :: .ident "revert_" :: .symbol '(' ::
              (dataOffset.tokens ++ .symbol ',' :: (size.tokens ++
                .symbol ')' :: .symbol ';' :: .symbol '}' :: rest)))))
        (fun name mem => names name (by simp [RollbackStmt.identifiers, mem]))
        (by simp only [RollbackStmt.size] at enough; omega) (by simp)
      simp only [RollbackStmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseLogIf, expectTokens, leftParse, BinaryOp.parse_token, rightParse, parseLetCall]

/-- No rollback statement reads as a store. -/
theorem parseStore_rollback (statement : RollbackStmt) (fuel : Nat) (rest : List Token) :
    parseStore fuel (statement.tokens ++ rest) = none := by
  cases statement with
  | storage statement =>
      cases statement with
      | plain statement =>
          cases statement <;>
            simp [RollbackStmt.tokens, StorageStmt.tokens, Stmt.tokens, parseStore, expectTokens]
      | letCall => simp [RollbackStmt.tokens, StorageStmt.tokens, parseStore, expectTokens]
      | store => simp [RollbackStmt.tokens, StorageStmt.tokens, parseStore, expectTokens]
  | letOperation => simp [RollbackStmt.tokens, parseStore, expectTokens]
  | revertIf => simp [RollbackStmt.tokens, parseStore, expectTokens]

theorem parseLogStmt_tokens (statement : LogStmt) (names : statement.NamesOk)
    (logger : statement.LoggerOk) (fuel : Nat) (enough : statement.size < fuel)
    (rest : List Token) :
    parseLogStmt fuel (statement.tokens ++ rest) = some (statement, rest) := by
  cases statement with
  | rollback statement =>
      have statementNames : statement.NamesOk := names
      have statementEnough : statement.size < fuel := enough
      simp only [LogStmt.tokens]
      simp [parseLogStmt, parseLogIf_rollback statement statementNames fuel statementEnough,
        parseStore_rollback statement fuel rest,
        parseRollbackStmt_tokens statement statementNames fuel statementEnough rest]
  | store offset value =>
      have notLog : parseLogIf fuel ((LogStmt.store offset value).tokens ++ rest) = none := by
        simp [LogStmt.tokens, storeTokens, parseLogIf, expectTokens]
      have parsed := parseStore_tokens offset value fuel rest names enough
      simp only [LogStmt.tokens] at notLog ⊢
      simp [parseLogStmt, notLog, parsed]
  | logIf op left right block =>
      have parsed := parseLogIf_tokens op left right block fuel rest names logger enough
      simp [parseLogStmt, parsed]

theorem LogStmt.blockEnds_tokens (statement : LogStmt) (names : statement.NamesOk)
    (rest : List Token) : blockEnds (statement.tokens ++ rest) = false := by
  cases statement with
  | rollback statement => exact RollbackStmt.blockEnds_tokens statement names rest
  | store => rfl
  | logIf => rfl

theorem parseLogStmts_tokens : ∀ (statements : List LogStmt) (fuel : Nat)
    (rest : List Token), LogStmt.ListNamesOk statements →
    (∀ statement ∈ statements, statement.LoggerOk) →
    LogStmt.listSize statements < fuel → blockEnds rest = true →
    parseLogStmts fuel (LogStmt.listTokens statements ++ rest) = some (statements, rest)
  | [], fuel + 1, rest, _, _, _, ends => by
      simp [LogStmt.listTokens, parseLogStmts, ends]
  | statement :: more, fuel + 1, rest, names, loggers, enough, ends => by
      have statementNames : statement.NamesOk :=
        fun name mem => names name (by simp [LogStmt.listIdentifiers, mem])
      have moreNames : LogStmt.ListNamesOk more :=
        fun name mem => names name (by simp [LogStmt.listIdentifiers, mem])
      have statementParse := parseLogStmt_tokens statement statementNames
        (loggers statement (by simp)) fuel (by simp only [LogStmt.listSize] at enough; omega)
        (LogStmt.listTokens more ++ rest)
      have moreParse := parseLogStmts_tokens more fuel rest moreNames
        (fun other mem => loggers other (by simp [mem]))
        (by simp only [LogStmt.listSize] at enough; omega) ends
      simp only [LogStmt.listTokens, List.append_assoc]
      simp [parseLogStmts, LogStmt.blockEnds_tokens statement statementNames,
        statementParse, moreParse]

theorem parseLogImport_tokens (aliases : List (String × String)) (rest : List Token) :
    parseLogImport (logImportTokens aliases ++ rest) = some (aliases, rest) := by
  cases aliases with
  | nil => simp [logImportTokens, storageAliasTokens, parseLogImport, expectTokens]
  | cons alias more =>
      have length := aliasTokens_length (alias :: more)
      simp only [logImportTokens, storageAliasTokens, List.append_assoc, List.cons_append,
        List.nil_append]
      simp [parseLogImport, expectTokens]
      rw [parseAliasList_tokens (alias :: more) _ _ (by simp) (by omega) rfl]
      simp [expectTokens]

theorem storesSize_le_tokens : (stores : List (Operand × Operand)) →
    storesSize stores ≤ (storesTokens stores).length
  | [] => by simp [storesSize, storesTokens]
  | (offset, value) :: rest => by
      have := Operand.size_le_tokens offset
      have := Operand.size_le_tokens value
      have := storesSize_le_tokens rest
      simp only [storesSize, storesTokens, storeTokens, List.length_append, List.length_cons,
        List.length_nil]
      omega

theorem topicsSize_le_tokens : (topics : List Operand) →
    topicsSize topics ≤ (topicsTokens topics).length
  | [] => by simp [topicsSize, topicsTokens]
  | topic :: rest => by
      have := Operand.size_le_tokens topic
      have := topicsSize_le_tokens rest
      simp only [topicsSize, topicsTokens, List.length_append, List.length_cons]
      omega

theorem LogStmt.size_lt_tokens (statement : LogStmt) :
    statement.size < statement.tokens.length := by
  cases statement with
  | rollback statement => exact RollbackStmt.size_lt_tokens statement
  | store offset value =>
      have := Operand.size_le_tokens offset
      have := Operand.size_le_tokens value
      simp only [LogStmt.size, LogStmt.tokens, storeTokens, List.length_append,
        List.length_cons, List.length_nil]
      omega
  | logIf op left right block =>
      have := Expr.size_le_tokens left
      have := Expr.size_le_tokens right
      have := StorageStmt.size_lt_tokens block.binding
      have := storesSize_le_tokens block.stores
      have := Operand.size_le_tokens block.dataOffset
      have := Operand.size_le_tokens block.dataSize
      have := topicsSize_le_tokens block.topics
      simp only [LogStmt.size, LogBlock.size, LogStmt.tokens, LogBlock.tokens, List.length_append,
        List.length_cons, List.length_nil]
      omega

theorem LogStmt.listSize_le_tokens : (statements : List LogStmt) →
    LogStmt.listSize statements ≤ (LogStmt.listTokens statements).length
  | [] => by simp [LogStmt.listSize, LogStmt.listTokens]
  | statement :: rest => by
      have := LogStmt.size_lt_tokens statement
      have := LogStmt.listSize_le_tokens rest
      simp only [LogStmt.listSize, LogStmt.listTokens, List.length_append]
      omega

theorem parseLogFileWith_tokens (file : LogFile) (names : file.NamesOk) (fuel : Nat)
    (functionsFuel : ∀ function ∈ file.functions,
      Stmt.listSize function.body < fuel ∧ function.result.size < fuel)
    (bodyFuel : LogStmt.listSize file.method.body < fuel)
    (resultFuel : file.method.result.size < fuel) :
    parseLogFileWith fuel file.tokens = some file := by
  obtain ⟨functionsOk, contractOk, methodOk, parametersOk, bodyOk, loggersOk, resultOk⟩ := names
  have resultParse := parseOperand_tokens file.method.result fuel (.symbol ')')
    [.symbol ';', .symbol '}', .symbol '}'] resultOk resultFuel (Or.inl rfl)
  have bodyParse := parseLogStmts_tokens file.method.body fuel
    (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
      [.symbol ')', .symbol ';', .symbol '}', .symbol '}'])) bodyOk loggersOk bodyFuel rfl
  have parametersParse := parseParameters_tokens file.method.parameters
    (signatureTokens ++ (LogStmt.listTokens file.method.body ++
      (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
        [.symbol ')', .symbol ';', .symbol '}', .symbol '}'])))) parametersOk rfl
  have functionsLength := functions_length_le_tokens file.functions
  have functionsParse := parseFunctions_tokens file.functions (file.tokens.length + 1) fuel
    (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
      .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
        (signatureTokens ++ (LogStmt.listTokens file.method.body ++
          (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
            [.symbol ')', .symbol ';', .symbol '}', .symbol '}']))))))
    (fun function mem => ⟨functionsOk function mem, functionsFuel function mem⟩)
    (by simp only [LogFile.tokens, List.length_append] at functionsLength ⊢; omega)
    (by simp)
  have importParse := parseLogImport_tokens file.opcodeAliases
    (file.functions.flatMap FunctionDecl.tokens ++
      (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
        .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
          (signatureTokens ++ (LogStmt.listTokens file.method.body ++
            (.ident "return" :: .ident "uint256" :: .symbol '(' :: (file.method.result.tokens ++
              [.symbol ')', .symbol ';', .symbol '}', .symbol '}'])))))))
  unfold parseLogFileWith
  conv => lhs; arg 1; rw [LogFile.tokens]
  simp only [List.append_assoc, List.cons_append, List.nil_append, expectTokens_append,
    Option.bind_eq_bind, Option.bind_some]
  rw [importParse]
  simp only [Option.bind_some]
  rw [functionsParse]
  simp [expectTokens, parseName_cons contractOk, parseName_cons methodOk, parametersParse,
    expectTokens_append, bodyParse, resultParse]

/-- **Parser round trip.** Parsing the tokens of a log file with non-reserved
names and no logger named `mstore` returns that file. -/
theorem parseLogFile_tokens (file : LogFile) (names : file.NamesOk) :
    parseLogFile file.tokens = some file := by
  have bodySize := LogStmt.listSize_le_tokens file.method.body
  have resultSize := Operand.size_le_tokens file.method.result
  apply parseLogFileWith_tokens file names
  · intro function mem
    have := functions_sizes_le_tokens mem
    simp only [LogFile.tokens, List.length_append]
    omega
  · simp only [LogFile.tokens, List.length_append] at bodySize ⊢
    omega
  · simp only [LogFile.tokens, List.length_append, List.length_cons] at resultSize ⊢
    omega

/-! ### Printed pieces -/

def storePieces (indent : Nat) (offset value : Operand) : List Piece :=
  blanks indent ++ [word "mstore", sym '('] ++ offset.pieces ++ [sym ',', space] ++
    value.pieces ++ [sym ')', sym ';']

def storesLinePieces (indent : Nat) : List (Operand × Operand) → List (List Piece)
  | [] => []
  | (offset, value) :: rest => storePieces indent offset value :: storesLinePieces indent rest

def topicsPieces : List Operand → List Piece
  | [] => []
  | topic :: rest => sym ',' :: space :: (topic.pieces ++ topicsPieces rest)

def LogBlock.linePieces (indent : Nat) (block : LogBlock) : List (List Piece) :=
  block.binding.linePieces indent ++ storesLinePieces indent block.stores ++
    [blanks indent ++ [word block.logger, sym '('] ++ block.dataOffset.pieces ++
      [sym ',', space] ++ block.dataSize.pieces ++ topicsPieces block.topics ++
      [sym ')', sym ';']]

def LogStmt.linePieces (indent : Nat) : LogStmt → List (List Piece)
  | .rollback statement => statement.linePieces indent
  | .store offset value => [storePieces indent offset value]
  | .logIf op left right block =>
      [blanks indent ++ [word "if", space, sym '('] ++ (Operand.operation op left right).pieces ++
          [sym ')', space, sym '{']] ++
        block.linePieces (indent + 4) ++ [blanks indent ++ [sym '}']]

def LogStmt.listLinePieces (indent : Nat) : List LogStmt → List (List Piece)
  | [] => []
  | statement :: rest => statement.linePieces indent ++ LogStmt.listLinePieces indent rest

theorem storeLine_toList (indent : Nat) (offset value : Operand) :
    (storeLine indent offset value).toList = render (storePieces indent offset value) := by
  simp [storeLine, storePieces, indentLine_toList, render_append, render_blanks, render,
    Piece.chars, Token.chars, word, sym, space, Operand.print_toList]

theorem storesLines_toList (indent : Nat) : (stores : List (Operand × Operand)) →
    (storesLines indent stores).map String.toList = (storesLinePieces indent stores).map render
  | [] => rfl
  | (offset, value) :: rest => by
      simp [storesLines, storesLinePieces, storeLine_toList, storesLines_toList indent rest]

theorem topicsText_toList : (topics : List Operand) →
    (topicsText topics).toList = render (topicsPieces topics)
  | [] => rfl
  | topic :: rest => by
      simp [topicsText, topicsPieces, render_append, render, Piece.chars, Token.chars, sym,
        space, Operand.print_toList, topicsText_toList rest]

theorem LogBlock.lines_toList (indent : Nat) (block : LogBlock) :
    (block.lines indent).map String.toList = (block.linePieces indent).map render := by
  simp [LogBlock.lines, LogBlock.linePieces, StorageStmt.lines_toList, storesLines_toList,
    indentLine_toList, render_append, render_blanks, render, Piece.chars, Token.chars, word, sym,
    space, Operand.print_toList, topicsText_toList]

theorem LogStmt.lines_toList (indent : Nat) : (statement : LogStmt) →
    (statement.lines indent).map String.toList = (statement.linePieces indent).map render
  | .rollback statement => RollbackStmt.lines_toList indent statement
  | .store offset value => by
      simp [LogStmt.lines, LogStmt.linePieces, storeLine_toList]
  | .logIf op left right block => by
      simp [LogStmt.lines, LogStmt.linePieces, LogBlock.lines_toList, indentLine_toList,
        render_append, render_blanks, render, Piece.chars, Token.chars, word, sym, space,
        Operand.print_toList]

theorem LogStmt.listLines_toList (indent : Nat) : (statements : List LogStmt) →
    (LogStmt.listLines indent statements).map String.toList =
      (LogStmt.listLinePieces indent statements).map render
  | [] => rfl
  | statement :: rest => by
      simp [LogStmt.listLines, LogStmt.listLinePieces, LogStmt.lines_toList indent statement,
        LogStmt.listLines_toList indent rest]

theorem storePieces_tokens (indent : Nat) (offset value : Operand) :
    tokensOf (storePieces indent offset value) = storeTokens offset value := by
  simp [storePieces, storeTokens, tokensOf_append, tokensOf_blanks, tokensOf, word, sym, space,
    Operand.tokensOf_pieces]

theorem storesLinePieces_tokens (indent : Nat) : (stores : List (Operand × Operand)) →
    ((storesLinePieces indent stores).map tokensOf).flatten = storesTokens stores
  | [] => rfl
  | (offset, value) :: rest => by
      simp [storesLinePieces, storesTokens, storePieces_tokens,
        storesLinePieces_tokens indent rest]

theorem topicsPieces_tokens : (topics : List Operand) →
    tokensOf (topicsPieces topics) = topicsTokens topics
  | [] => rfl
  | topic :: rest => by
      simp [topicsPieces, topicsTokens, tokensOf_append, tokensOf, sym, space,
        Operand.tokensOf_pieces, topicsPieces_tokens rest]

theorem LogBlock.linePieces_tokens (indent : Nat) (block : LogBlock) :
    ((block.linePieces indent).map tokensOf).flatten = block.tokens := by
  simp [LogBlock.linePieces, LogBlock.tokens, StorageStmt.linePieces_tokens,
    storesLinePieces_tokens, tokensOf_append, tokensOf_blanks, tokensOf, word, sym, space,
    Operand.tokensOf_pieces, topicsPieces_tokens]

theorem LogStmt.linePieces_tokens (indent : Nat) : (statement : LogStmt) →
    ((statement.linePieces indent).map tokensOf).flatten = statement.tokens
  | .rollback statement => RollbackStmt.linePieces_tokens indent statement
  | .store offset value => by
      simp [LogStmt.linePieces, LogStmt.tokens, storePieces_tokens]
  | .logIf op left right block => by
      simp [LogStmt.linePieces, LogStmt.tokens, LogBlock.linePieces_tokens, tokensOf_append,
        tokensOf_blanks, tokensOf, word, sym, space, Operand.tokensOf_pieces, Operand.tokens]

theorem LogStmt.listLinePieces_tokens (indent : Nat) : (statements : List LogStmt) →
    ((LogStmt.listLinePieces indent statements).map tokensOf).flatten =
      LogStmt.listTokens statements
  | [] => rfl
  | statement :: rest => by
      simp [LogStmt.listLinePieces, LogStmt.listTokens, LogStmt.linePieces_tokens indent statement,
        LogStmt.listLinePieces_tokens indent rest]

theorem storesLinePieces_separated (indent : Nat) : (stores : List (Operand × Operand)) →
    (∀ name ∈ storesIdentifiers stores, ValidIdentifier name) →
    ∀ line ∈ storesLinePieces indent stores, Separated line
  | [], _, _, mem => by simp [storesLinePieces] at mem
  | (offset, value) :: rest, valid, line, mem => by
      simp only [storesLinePieces, List.mem_cons] at mem
      rcases mem with same | mem
      · subst same
        exact callPieces_separated indent "mstore" (keyword_valid (by decide)) offset value
          (fun name found => valid name (by simp [storesIdentifiers, found]))
          (fun name found => valid name (by simp [storesIdentifiers, found]))
      · exact storesLinePieces_separated indent rest
          (fun name found => valid name (by simp [storesIdentifiers, found])) line mem

/-- The topics and the closing `);` of a log line are separated, and start with
a symbol. -/
theorem topicsPieces_separated : (topics : List Operand) →
    (∀ name ∈ topicsIdentifiers topics, ValidIdentifier name) →
    Separated (topicsPieces topics ++ [sym ')', sym ';']) ∧
      ∀ next ∈ (topicsPieces topics ++ [sym ')', sym ';']).head?, next.SafeLeft
  | [], _ => ⟨Separated.cons_sym (by decide) (sym_valid (by decide)), head_sym (by decide)⟩
  | topic :: rest, valid => by
      have restPart := topicsPieces_separated rest
        (fun name found => valid name (by simp [topicsIdentifiers, found]))
      have topicPart := Operand.separated_append topic
        (fun name found => valid name (by simp [topicsIdentifiers, found])) _ restPart.1
        restPart.2
      simp only [topicsPieces, List.cons_append, List.append_assoc] at topicPart ⊢
      exact ⟨Separated.cons_sym (by decide) (Separated.cons_space topicPart),
        head_sym (by decide)⟩

theorem LogBlock.linePieces_separated (indent : Nat) (block : LogBlock)
    (valid : ∀ name ∈ block.identifiers, ValidIdentifier name) :
    ∀ line ∈ block.linePieces indent, Separated line := by
  intro line mem
  simp only [LogBlock.linePieces, List.mem_append, List.mem_singleton] at mem
  rcases mem with (mem | mem) | same
  · exact StorageStmt.linePieces_separated indent block.binding
      (fun name found => valid name (by simp [LogBlock.identifiers, found])) line mem
  · exact storesLinePieces_separated indent block.stores
      (fun name found => valid name (by simp [LogBlock.identifiers, found])) line mem
  · subst same
    have topicsPart := topicsPieces_separated block.topics
      (fun name found => valid name (by simp [LogBlock.identifiers, found]))
    have sizePart := Operand.separated_append block.dataSize
      (fun name found => valid name (by simp [LogBlock.identifiers, found])) _ topicsPart.1
      topicsPart.2
    have offsetPart := Operand.separated_append block.dataOffset
      (fun name found => valid name (by simp [LogBlock.identifiers, found]))
      (sym ',' :: space :: (block.dataSize.pieces ++ (topicsPieces block.topics ++
        [sym ')', sym ';'])))
      (Separated.cons_sym (by decide) (Separated.cons_space sizePart)) (head_sym (by decide))
    simp only [List.append_assoc, List.cons_append, List.nil_append] at offsetPart ⊢
    exact Separated.blanks_append indent (Separated.cons_word
      (valid block.logger (by simp [LogBlock.identifiers]))
      (Separated.cons_sym (by decide) offsetPart) (head_sym (by decide)))

theorem LogStmt.linePieces_separated (indent : Nat) : (statement : LogStmt) →
    (∀ name ∈ statement.identifiers, ValidIdentifier name) →
    ∀ line ∈ statement.linePieces indent, Separated line
  | .rollback statement, valid, line, mem =>
      RollbackStmt.linePieces_separated indent statement valid line mem
  | .store offset value, valid, line, mem => by
      simp only [LogStmt.linePieces, List.mem_singleton] at mem
      subst mem
      exact callPieces_separated indent "mstore" (keyword_valid (by decide)) offset value
        (fun name found => valid name (by simp [LogStmt.identifiers, found]))
        (fun name found => valid name (by simp [LogStmt.identifiers, found]))
  | .logIf op left right block, valid, line, mem => by
      simp only [LogStmt.linePieces, List.mem_append, List.mem_singleton] at mem
      rcases mem with (same | mem) | same
      · subst same
        have operation := Operand.separated_append (.operation op left right)
          (fun name found => by
            simp only [Operand.identifiers, List.mem_append] at found
            rcases found with found | found
            · exact valid name (by simp [LogStmt.identifiers, found])
            · exact valid name (by simp [LogStmt.identifiers, found]))
          [sym ')', space, sym '{'] (Separated.cons_sym (by decide) (Separated.cons_space
            (sym_valid (by decide)))) (head_sym (by decide))
        simp only [List.append_assoc, List.cons_append, List.nil_append] at operation ⊢
        exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_space (Separated.cons_sym (by decide) operation)) head_space)
      · exact LogBlock.linePieces_separated (indent + 4) block
          (fun name found => valid name (by simp [LogStmt.identifiers, found])) line mem
      · subst same
        exact Separated.blanks_append indent (sym_valid (by decide))

theorem LogStmt.listLinePieces_separated (indent : Nat) :
    (statements : List LogStmt) →
    (∀ name ∈ LogStmt.listIdentifiers statements, ValidIdentifier name) →
    ∀ line ∈ LogStmt.listLinePieces indent statements, Separated line
  | [], _, _, mem => by simp [LogStmt.listLinePieces] at mem
  | statement :: rest, valid, line, mem => by
      simp only [LogStmt.listLinePieces, List.mem_append] at mem
      rcases mem with mem | mem
      · exact LogStmt.linePieces_separated indent statement
          (fun name found => valid name (by simp [LogStmt.listIdentifiers, found])) line mem
      · exact LogStmt.listLinePieces_separated indent rest
          (fun name found => valid name (by simp [LogStmt.listIdentifiers, found])) line mem

def logImportPieces (aliases : List (String × String)) : List Piece :=
  [word "import", space, sym '{', word "sload", sym ',', space, word "sstore", sym ',', space,
    word "mload", sym ',', space, word "mstore", sym ',', space, word "revert_"] ++
    storageAliasPieces aliases ++
    [sym '}', space, word "from", space, word "std", sym '.', word "opcodes", sym ';']

theorem logImportLine_toList (aliases : List (String × String)) :
    (logImportLine aliases).toList = render (logImportPieces aliases) := by
  cases aliases with
  | nil =>
      simp [logImportLine, logImportPieces, storageAliasPieces, String.intercalate_cons_cons,
        render, Piece.chars, Token.chars, word, sym, space]
  | cons alias more =>
      have tail := aliasText_toList (alias :: more)
      simp only [List.map_cons] at tail
      simp only [logImportLine, List.cons_append, List.nil_append, List.map_cons]
      rw [String.intercalate_cons_cons, String.intercalate_cons_cons,
        String.intercalate_cons_cons, String.intercalate_cons_cons,
        String.intercalate_cons_cons]
      simp only [String.toList_append, tail]
      simp [logImportPieces, storageAliasPieces, render_append, render, Piece.chars,
        Token.chars, word, sym, space]

theorem logImportPieces_tokens (aliases : List (String × String)) :
    tokensOf (logImportPieces aliases) = logImportTokens aliases := by
  cases aliases <;>
    simp [logImportPieces, storageAliasPieces, logImportTokens, storageAliasTokens,
      tokensOf_append, tokensOf, word, sym, space, aliasPieces_tokens]

theorem logImportPieces_separated (aliases : List (String × String))
    (valid : ∀ alias ∈ aliases, ValidIdentifier alias.1 ∧ ValidIdentifier alias.2) :
    Separated (logImportPieces aliases) := by
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
  simp only [logImportPieces, List.cons_append, List.nil_append]
  exact Separated.cons_word (keyword_valid (by decide)) (Separated.cons_space
    (Separated.cons_sym (by decide) (Separated.cons_word (keyword_valid (by decide))
      (Separated.cons_sym (by decide) (Separated.cons_space (Separated.cons_word
        (keyword_valid (by decide)) (Separated.cons_sym (by decide) (Separated.cons_space
          (Separated.cons_word (keyword_valid (by decide)) (Separated.cons_sym (by decide)
            (Separated.cons_space (Separated.cons_word (keyword_valid (by decide))
              (Separated.cons_sym (by decide) (Separated.cons_space (Separated.cons_word
                (keyword_valid (by decide)) middle.1 middle.2)))
              (head_sym (by decide))))) (head_sym (by decide))))) (head_sym (by decide)))))
      (head_sym (by decide))))) head_space

def LogFile.linePieces (file : LogFile) : List (List Piece) :=
  [[word "import", space, sym '*', space, word "from", space, word "std", sym ';'],
    [word "import", space, sym '*', space, word "from", space, word "std", sym '.',
      word "dispatch", sym ';']] ++
  [logImportPieces file.opcodeAliases] ++ [[]] ++
  file.functions.flatMap FunctionDecl.linePieces ++
  [[word "contract", space, word file.contract, space, sym '{'],
    blanks 4 ++ [word "function", space, word file.method.name, sym '('] ++
      parameterPieces file.method.parameters ++
      [sym ')', space, word "public", space, word "returns", space, sym '(', word "uint256",
        sym ')', space, sym '{']] ++
  LogStmt.listLinePieces 8 file.method.body ++
  [blanks 8 ++ [word "return", space, word "uint256", sym '('] ++ file.method.result.pieces ++
      [sym ')', sym ';'],
    blanks 4 ++ [sym '}'], [sym '}']]

theorem LogFile.lines_toList (file : LogFile) :
    file.lines.map String.toList = file.linePieces.map render := by
  simp only [LogFile.lines, LogFile.linePieces, List.map_append, functions_lines_toList]
  simp [LogStmt.listLines_toList, parameterText_toList, Operand.print_toList,
    logImportLine_toList, render_append, render_blanks, render, Piece.chars, Token.chars,
    word, sym, space]

theorem LogFile.linePieces_tokens (file : LogFile) :
    (file.linePieces.map tokensOf).flatten = file.tokens := by
  simp only [LogFile.linePieces, LogFile.tokens, List.map_append, List.flatten_append,
    functions_linePieces_tokens]
  simp [importTokens, signatureTokens, LogStmt.listLinePieces_tokens,
    parameterPieces_tokens, Operand.tokensOf_pieces, logImportPieces_tokens,
    tokensOf_append, tokensOf_blanks, tokensOf, word, sym, space]

/-- Every identifier of the log file is lexically valid. -/
def LogFile.IdentifiersValid (file : LogFile) : Prop :=
  (∀ alias ∈ file.opcodeAliases, ValidIdentifier alias.1 ∧ ValidIdentifier alias.2) ∧
    (∀ function ∈ file.functions, ∀ name ∈ function.identifiers, ValidIdentifier name) ∧
    ValidIdentifier file.contract ∧ ValidIdentifier file.method.name ∧
    (∀ parameter ∈ file.method.parameters, ValidIdentifier parameter) ∧
    (∀ name ∈ LogStmt.listIdentifiers file.method.body, ValidIdentifier name) ∧
    (∀ name ∈ file.method.result.identifiers, ValidIdentifier name)

/-- The log file without aliases, method body or returned operand. Its lines
are the log file's import, function, contract and closing lines. -/
def LogFile.skeleton (file : LogFile) : SourceFile where
  opcodeAliases := []
  functions := file.functions
  contract := file.contract
  method := {
    name := file.method.name, parameters := file.method.parameters, body := [],
    result := .number 0 }

theorem LogFile.linePieces_separated (file : LogFile)
    (valid : file.IdentifiersValid) : ∀ line ∈ file.linePieces, Separated line := by
  obtain ⟨aliasesValid, functionsValid, contractValid, methodValid, parametersValid, bodyValid,
    resultValid⟩ := valid
  have skeleton := file.skeleton.linePieces_separated ⟨by simp [LogFile.skeleton],
    functionsValid, contractValid, methodValid, parametersValid,
    by simp [LogFile.skeleton, Stmt.listIdentifiers],
    by simp [LogFile.skeleton, Expr.identifiers]⟩
  intro line mem
  unfold LogFile.linePieces at mem
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
              exact logImportPieces_separated _ aliasesValid
          · simp only [List.mem_singleton] at mem
            subst mem
            trivial
        · exact skeleton line (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_right _ mem))))
      · exact skeleton line (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ mem)))
    · exact LogStmt.listLinePieces_separated 8 file.method.body bodyValid line mem
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

theorem LogFile.print_toList (file : LogFile) :
    file.print.toList = render (joinLines file.linePieces) := by
  rw [LogFile.print, String.toList_append, String.toList_intercalate, joinLines,
    render_append, render_intercalate, LogFile.lines_toList]
  rfl

/-- **Text round trip.** The printed text of a log file with lexically valid,
non-reserved names and no logger named `mstore` parses back to that file. -/
theorem parseLogSource_print (file : LogFile) (names : file.NamesOk)
    (valid : file.IdentifiersValid) : parseLogSource file.print = some file := by
  rw [parseLogSource, LogFile.print_toList,
    lex_render (joinLines_separated _ (file.linePieces_separated valid)), Option.bind_some,
    tokensOf_joinLines, LogFile.linePieces_tokens]
  exact parseLogFile_tokens file names

/-- The meaning of a printed log file's text is the meaning of the file. -/
theorem logSourceCall_print (file : LogFile) (names : file.NamesOk)
    (valid : file.IdentifiersValid) (storage : Storage) (memory : Memory) (method : String)
    (arguments : List Nat) :
    logSourceCall file.print storage memory method arguments =
      file.call storage memory method arguments := by
  simp [logSourceCall, parseLogSource_print file names valid]

end Solcore.Synthesis.Source.ScalarMeaning
end
