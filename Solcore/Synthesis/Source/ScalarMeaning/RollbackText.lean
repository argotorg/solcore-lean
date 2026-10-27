import Solcore.Synthesis.Source.ScalarMeaning.RollbackSemantics
import Solcore.Synthesis.Source.ScalarMeaning.StorageText

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
