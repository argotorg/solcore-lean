import Solcore.Synthesis.Source.ScalarMeaning.LogSemantics
import Solcore.Synthesis.Source.ScalarMeaning.RollbackText

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
