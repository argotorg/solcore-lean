import Solcore.Synthesis.Source.ScalarMeaning.Lex
import Solcore.Synthesis.Source.ScalarMeaning.Syntax

/-! Token grammar and recursive-descent parser for the scalar source
fragment. Operator applications are fully parenthesized, statement blocks end
at `}` and the method body ends at `return`. `parseFile` inverts the token
printing of every file whose names are not reserved words. -/
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

def headerTokens : List Token :=
  [.ident "import", .symbol '*', .ident "from", .ident "std", .symbol ';',
    .ident "import", .symbol '*', .ident "from", .ident "std", .symbol '.', .ident "dispatch",
    .symbol ';', .ident "contract"]

def signatureTokens : List Token :=
  [.symbol ')', .ident "public", .ident "returns", .symbol '(', .ident "uint256", .symbol ')',
    .symbol '{']

def SourceFile.tokens (file : SourceFile) : List Token :=
  headerTokens ++ [.ident file.contract, .symbol '{', .ident "function", .ident file.method.name,
    .symbol '('] ++ parameterTokens file.method.parameters ++ signatureTokens ++
    Stmt.listTokens file.method.body ++ [.ident "return"] ++ file.method.result.tokens ++
    [.symbol ';', .symbol '}', .symbol '}']

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

def parseFileWith (fuel : Nat) (tokens : List Token) : Option SourceFile := do
  let rest ← expectTokens headerTokens tokens
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
  if rest = [] then some { contract, method := { name := method, parameters, body, result } }
  else none

/-- Parse a complete token stream; one more than its length bounds nesting. -/
def parseFile (tokens : List Token) : Option SourceFile :=
  parseFileWith (tokens.length + 1) tokens

/-! ### Sizes -/

def Expr.size : Expr → Nat
  | .name _ | .number _ | .bool _ => 1
  | .unary _ operand | .typedefRep operand | .uint256 operand => operand.size + 1
  | .binary _ left right => left.size + right.size + 1

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

theorem LocalType.parse_token (type : LocalType) :
    parseLocalType? (.ident type.spelling) = some type := by
  cases type <;> rfl

/-- Every name in the expression is a non-reserved word. -/
def Expr.NamesOk (expression : Expr) : Prop :=
  ∀ name ∈ expression.identifiers, isReserved name = false

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

theorem parseExpr_tokens : ∀ (expression : Expr) (fuel : Nat) (rest : List Token),
    expression.NamesOk → expression.size < fuel →
    parseExpr fuel (expression.tokens ++ rest) = some (expression, rest)
  | .name identifier, fuel + 1, rest, names, _ => by
      have notReserved : isReserved identifier = false :=
        names identifier (by simp [Expr.identifiers])
      have notTrue : identifier ≠ "true" := fun same => by
        subst same
        simp [isReserved, reservedWords] at notReserved
      have notFalse : identifier ≠ "false" := fun same => by
        subst same
        simp [isReserved, reservedWords] at notReserved
      have notTypedef : identifier ≠ "Typedef" := fun same => by
        subst same
        simp [isReserved, reservedWords] at notReserved
      have notUint : identifier ≠ "uint256" := fun same => by
        subst same
        simp [isReserved, reservedWords] at notReserved
      simp [Expr.tokens, parseExpr, notTrue, notFalse, notTypedef, notUint, notReserved]
  | .number value, fuel + 1, rest, _, _ => by simp [Expr.tokens, parseExpr]
  | .bool value, fuel + 1, rest, _, _ => by cases value <;> simp [Expr.tokens, parseExpr]
  | .unary op operand, fuel + 1, rest, names, enough => by
      have operandParse := parseExpr_tokens operand fuel ([.symbol ')'] ++ rest)
        (fun name mem => names name (by simpa [Expr.identifiers] using mem))
        (by simp only [Expr.size] at enough; omega)
      simp only [Expr.tokens, List.append_assoc, List.cons_append,
        List.nil_append] at operandParse ⊢
      simp [parseExpr, UnaryOp.parse_token, operandParse, expectTokens]
  | .binary op left right, fuel + 1, rest, names, enough => by
      have rightParse := parseExpr_tokens right fuel ([.symbol ')'] ++ rest)
        (fun name mem => names name (by simp [Expr.identifiers, mem]))
        (by simp only [Expr.size] at enough; omega)
      have leftParse := parseExpr_tokens left fuel
        ([op.token] ++ right.tokens ++ [.symbol ')'] ++ rest)
        (fun name mem => names name (by simp [Expr.identifiers, mem]))
        (by simp only [Expr.size] at enough; omega)
      obtain ⟨first, tail, head, notUnary⟩ := Expr.tokens_head left
      simp only [List.append_assoc, List.cons_append, List.nil_append] at leftParse rightParse
      rw [head, List.cons_append] at leftParse
      simp only [Expr.tokens, head, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseExpr, notUnary, leftParse, BinaryOp.parse_token, rightParse, expectTokens]
  | .typedefRep operand, fuel + 1, rest, names, enough => by
      have operandParse := parseExpr_tokens operand fuel ([.symbol ')'] ++ rest)
        (fun name mem => names name (by simpa [Expr.identifiers] using mem))
        (by simp only [Expr.size] at enough; omega)
      simp only [Expr.tokens, List.append_assoc, List.cons_append,
        List.nil_append] at operandParse ⊢
      simp [parseExpr, operandParse, expectTokens]
  | .uint256 operand, fuel + 1, rest, names, enough => by
      have operandParse := parseExpr_tokens operand fuel ([.symbol ')'] ++ rest)
        (fun name mem => names name (by simpa [Expr.identifiers] using mem))
        (by simp only [Expr.size] at enough; omega)
      simp only [Expr.tokens, List.append_assoc, List.cons_append,
        List.nil_append] at operandParse ⊢
      simp [parseExpr, operandParse, expectTokens]
  | _, 0, _, _, enough => absurd enough (Nat.not_lt_zero _)

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
              (by simp only [Stmt.size] at enough; omega)
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
              (by simp only [Stmt.size] at enough; omega)
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
              (by simp only [Stmt.size] at enough; omega)
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

def SourceFile.NamesOk (file : SourceFile) : Prop :=
  isReserved file.contract = false ∧ isReserved file.method.name = false ∧
    (∀ parameter ∈ file.method.parameters, isReserved parameter = false) ∧
    Stmt.ListNamesOk file.method.body ∧ file.method.result.NamesOk

theorem parseFileWith_tokens (file : SourceFile) (names : file.NamesOk) (fuel : Nat)
    (bodyFuel : Stmt.listSize file.method.body < fuel)
    (resultFuel : file.method.result.size < fuel) :
    parseFileWith fuel file.tokens = some file := by
  obtain ⟨contractOk, methodOk, parametersOk, bodyOk, resultOk⟩ := names
  have bodyParse := parseStmts_tokens (fuel := fuel)
    (rest := .ident "return" :: (file.method.result.tokens ++
      [.symbol ';', .symbol '}', .symbol '}'])) bodyOk bodyFuel rfl
  have resultParse := parseExpr_tokens file.method.result fuel
    [.symbol ';', .symbol '}', .symbol '}'] resultOk resultFuel
  have parametersParse := parseParameters_tokens file.method.parameters
    (signatureTokens ++ (Stmt.listTokens file.method.body ++ (.ident "return" ::
      (file.method.result.tokens ++ [.symbol ';', .symbol '}', .symbol '}'])))) parametersOk rfl
  simp only [parseFileWith, SourceFile.tokens, List.append_assoc, List.cons_append,
    List.nil_append, expectTokens_append]
  simp [parseName_cons contractOk, parseName_cons methodOk, expectTokens, parametersParse,
    expectTokens_append, bodyParse, resultParse]

/-- **Parser round trip.** Parsing the tokens of a file with non-reserved
names returns that file. -/
theorem parseFile_tokens (file : SourceFile) (names : file.NamesOk) :
    parseFile file.tokens = some file := by
  have bodySize := Stmt.listSize_le_tokens file.method.body
  have resultSize := Expr.size_le_tokens file.method.result
  apply parseFileWith_tokens file names
  · simp only [SourceFile.tokens, List.length_append] at bodySize ⊢
    omega
  · simp only [SourceFile.tokens, List.length_append] at resultSize ⊢
    omega

end Solcore.Synthesis.Source.ScalarMeaning
