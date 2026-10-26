import Solcore.Synthesis.Source.ScalarMeaning.Lex
import Solcore.Synthesis.Source.ScalarMeaning.Syntax

/-! Token grammar and recursive-descent parser for the scalar source
fragment. Operator applications are fully parenthesized, a name followed by
`(` is a call, statement blocks end at `}` and function bodies end at
`return`. `parseFile` inverts the token printing of every file whose names
are not reserved words. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

/-- Words that cannot name contracts, methods, parameters or locals. -/
def reservedWords : List String :=
  ["let", "if", "else", "return", "true", "false", "Typedef", "rep", "uint256", "word", "bool",
    "import", "from", "contract", "function", "public", "returns"]

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

mutual

def Stmt.tokens : Stmt → List Token
  | .letDecl identifier type initializer =>
      [.ident "let", .ident identifier, .symbol ':', .ident type.spelling, .symbol '='] ++
        initializer.tokens ++ [.symbol ';']
  | .assign identifier value => [.ident identifier, .symbol '='] ++ value.tokens ++ [.symbol ';']
  | .ifElse condition thenBlock elseBlock =>
      [.ident "if", .symbol '('] ++ condition.tokens ++ [.symbol ')', .symbol '{'] ++
        Stmt.listTokens thenBlock ++ [.symbol '}', .ident "else", .symbol '{'] ++
        Stmt.listTokens elseBlock ++ [.symbol '}']

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

def importTokens : List Token :=
  [.ident "import", .symbol '*', .ident "from", .ident "std", .symbol ';',
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
  | [parameter] => [.ident parameter.1, .symbol ':', .ident parameter.2.spelling]
  | parameter :: next :: rest =>
      [.ident parameter.1, .symbol ':', .ident parameter.2.spelling, .symbol ','] ++
        typedParameterTokens (next :: rest)

def FunctionDecl.tokens (function : FunctionDecl) : List Token :=
  [.ident "function", .ident function.name, .symbol '('] ++
    typedParameterTokens function.parameters ++
    [.symbol ')', .ident "returns", .symbol '(', .ident function.resultType.spelling,
      .symbol ')', .symbol '{'] ++
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

def parseLocalType? : Token → Option LocalType
  | .ident text => if text = "word" then some .word else if text = "bool" then some .bool else none
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
                | opToken :: rest => do
                    let op ← parseBinaryOp? opToken
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
            let type ← (rest.head?).bind parseLocalType?
            let rest ← expectTokens [.symbol '='] rest.tail
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
      let type ← rest.head?.bind parseLocalType?
      if rest.tail.head? = some (.symbol ',') then do
        let (parameters, rest) ← parseTypedParameterList fuel rest.tail.tail
        some ((parameter, type) :: parameters, rest)
      else some ([(parameter, type)], rest.tail)

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
  let resultType ← rest.head?.bind parseLocalType?
  let rest ← expectTokens [.symbol ')', .symbol '{'] rest.tail
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

mutual

def Stmt.size : Stmt → Nat
  | .letDecl _ _ initializer => initializer.size + 1
  | .assign _ value => value.size + 1
  | .ifElse condition thenBlock elseBlock =>
      condition.size + Stmt.listSize thenBlock + Stmt.listSize elseBlock + 1

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

theorem LocalType.parse_token (type : LocalType) :
    parseLocalType? (.ident type.spelling) = some type := by
  cases type <;> rfl

/-- Every name in the expression is a non-reserved word. -/
def Expr.NamesOk (expression : Expr) : Prop :=
  ∀ name ∈ expression.identifiers, isReserved name = false

theorem not_reserved_names {text : String} (notReserved : isReserved text = false) :
    text ≠ "true" ∧ text ≠ "false" ∧ text ≠ "Typedef" ∧ text ≠ "uint256" := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro same <;> subst same <;>
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

/-- Expression round trip. The next token must not be `(`, which would turn
a final name into a call; every printed context satisfies this. -/
theorem parseExpr_tokens : ∀ (expression : Expr) (fuel : Nat) (rest : List Token),
    expression.NamesOk → expression.size < fuel → rest.head? ≠ some (.symbol '(') →
    parseExpr fuel (expression.tokens ++ rest) = some (expression, rest)
  | .name identifier, fuel + 1, rest, names, _, notOpen => by
      have notReserved : isReserved identifier = false :=
        names identifier (by simp [Expr.identifiers])
      obtain ⟨notTrue, notFalse, notTypedef, notUint⟩ := not_reserved_names notReserved
      simp [Expr.tokens, parseExpr, notTrue, notFalse, notTypedef, notUint, notReserved,
        notOpen]
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
      simp [parseExpr, notUnary, leftParse, BinaryOp.parse_token, rightParse, expectTokens]
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
      obtain ⟨notTrue, notFalse, notTypedef, notUint⟩ := not_reserved_names calleeOk
      have firstParse := parseExpr_tokens first fuel ([.symbol ')'] ++ rest)
        (fun name mem => names name (by simp [Expr.identifiers, mem]))
        (by simp only [Expr.size] at enough; omega) (by simp)
      simp only [List.cons_append, List.nil_append] at firstParse
      simp only [Expr.tokens, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseExpr, notTrue, notFalse, notTypedef, notUint, calleeOk, firstParse]
  | .call2 callee first second, fuel + 1, rest, names, enough, _ => by
      have calleeOk : isReserved callee = false := names callee (by simp [Expr.identifiers])
      obtain ⟨notTrue, notFalse, notTypedef, notUint⟩ := not_reserved_names calleeOk
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
      simp [parseExpr, notTrue, notFalse, notTypedef, notUint, calleeOk, firstParse,
        secondParse]
  | .call3 callee first second third, fuel + 1, rest, names, enough, _ => by
      have calleeOk : isReserved callee = false := names callee (by simp [Expr.identifiers])
      obtain ⟨notTrue, notFalse, notTypedef, notUint⟩ := not_reserved_names calleeOk
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
      simp [parseExpr, notTrue, notFalse, notTypedef, notUint, calleeOk, firstParse,
        secondParse, thirdParse, expectTokens]
  | _, 0, _, _, enough, _ => absurd enough (Nat.not_lt_zero _)

def Stmt.NamesOk (statement : Stmt) : Prop :=
  ∀ name ∈ statement.identifiers, isReserved name = false

def Stmt.ListNamesOk (statements : List Stmt) : Prop :=
  ∀ name ∈ Stmt.listIdentifiers statements, isReserved name = false

theorem not_reserved_ne {text : String} (notReserved : isReserved text = false) :
    text ≠ "let" ∧ text ≠ "if" ∧ text ≠ "return" := by
  refine ⟨?_, ?_, ?_⟩ <;> intro same <;> subst same <;>
    simp [isReserved, reservedWords] at notReserved

theorem Stmt.blockEnds_tokens (statement : Stmt) (names : statement.NamesOk)
    (rest : List Token) : blockEnds (statement.tokens ++ rest) = false := by
  cases statement with
  | letDecl identifier type initializer => rfl
  | assign identifier value =>
      have notReserved : isReserved identifier = false :=
        names identifier (by simp [Stmt.identifiers])
      have notReturn := (not_reserved_ne notReserved).2.2
      simp [Stmt.tokens, blockEnds, notReturn]
  | ifElse condition thenBlock elseBlock => rfl

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
            simp [parseStmt, parseName_cons notReserved, expectTokens, LocalType.parse_token,
              initializerParse]
        | assign identifier value =>
            have notReserved : isReserved identifier = false :=
              names identifier (by simp [Stmt.identifiers])
            obtain ⟨notLet, notIf, _⟩ := not_reserved_ne notReserved
            have valueParse := parseExpr_tokens value fuel ([.symbol ';'] ++ rest)
              (fun name mem => names name (by simp [Stmt.identifiers, mem]))
              (by simp only [Stmt.size] at enough; omega) (by simp)
            simp only [Stmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
              at valueParse ⊢
            simp [parseStmt, notLet, notIf, notReserved, expectTokens, valueParse]
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
            expectTokens, LocalType.parse_token]
  | parameter :: next :: more, fuel + 1, rest, _, names, enough, closing => by
      have notReserved := names parameter (by simp)
      have tailParse := parseTypedParameterList_tokens (next :: more) fuel rest (by simp)
        (fun name mem => names name (List.mem_cons_of_mem _ mem))
        (by simp only [List.length_cons] at enough ⊢; omega) closing
      simp only [typedParameterTokens, List.cons_append, List.nil_append]
      simp [parseTypedParameterList, parseName_cons notReserved, expectTokens,
        LocalType.parse_token, tailParse]
  | _ :: _, 0, _, _, _, enough, _ => absurd enough (by simp)

theorem typedParameterTokens_length : (parameters : List (String × LocalType)) →
    parameters.length ≤ (typedParameterTokens parameters).length
  | [] => Nat.le_refl _
  | [_] => by simp [typedParameterTokens]
  | _ :: next :: more => by
      have := typedParameterTokens_length (next :: more)
      simp only [typedParameterTokens, List.length_append, List.length_cons] at this ⊢
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
    (.symbol ')' :: .ident "returns" :: .symbol '(' :: .ident function.resultType.spelling ::
      .symbol ')' :: .symbol '{' :: (Stmt.listTokens function.body ++ (.ident "return" ::
        (function.result.tokens ++ (.symbol ';' :: .symbol '}' :: rest))))) parametersOk rfl
  simp only [parseFunction, FunctionDecl.tokens, List.append_assoc, List.cons_append,
    List.nil_append]
  simp [expectTokens, parseName_cons nameOk, parametersParse, LocalType.parse_token,
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
