import Solcore.Synthesis.Source.ScalarMeaning.GenericSemantics
import Solcore.Synthesis.Source.ScalarMeaning.Text

/-! Text of generic programs. `parseGenericSource` lexes a complete text as
`parseSource` does and parses it with the same grammar, extended by generic
functions after the imports, guards in their bodies and infix statements in the
method body. Each extension is recognized from its first tokens: a generic
function has `<` after its name where an ordinary one has `(`; a guard starts
with `if ( name ) { return`, which no loop-free statement starts with; and an
infix statement goes on with an infix operator where a `let` or an assignment
would end with `;`. The printed text of every generic file with valid,
non-reserved names, at least one type parameter per generic function and no
`match` printed as a leaf parses back to that file. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

/-! ### Tokens -/

def TypeRef.tokens : TypeRef → List Token
  | .concrete type => type.tokens
  | .param name => [.ident name]

def typeParameterTokens : List String → List Token
  | [] => []
  | [name] => [.ident name]
  | name :: next :: rest => [.ident name, .symbol ','] ++ typeParameterTokens (next :: rest)

def genericParameterTokens : List (String × TypeRef) → List Token
  | [] => []
  | [parameter] => [.ident parameter.1, .symbol ':'] ++ parameter.2.tokens
  | parameter :: next :: rest =>
      [.ident parameter.1, .symbol ':'] ++ parameter.2.tokens ++ [.symbol ','] ++
        genericParameterTokens (next :: rest)

/-- The tokens that start a guard on the local `name`. -/
def guardTokens (name : String) : List Token :=
  [.ident "if", .symbol '(', .ident name, .symbol ')', .symbol '{', .ident "return"]

def GuardStmt.tokens : GuardStmt → List Token
  | .plain statement => statement.tokens
  | .guard condition value =>
      guardTokens condition ++ value.tokens ++ [.symbol ';', .symbol '}']

def GuardStmt.listTokens : List GuardStmt → List Token
  | [] => []
  | statement :: rest => statement.tokens ++ GuardStmt.listTokens rest

def GenericDecl.tokens (declaration : GenericDecl) : List Token :=
  [.ident "function", .ident declaration.name, .symbol '<'] ++
    typeParameterTokens declaration.typeParameters ++ [.symbol '>', .symbol '('] ++
    genericParameterTokens declaration.parameters ++
    [.symbol ')', .ident "returns", .symbol '('] ++ declaration.resultType.tokens ++
    [.symbol ')', .symbol '{'] ++ GuardStmt.listTokens declaration.body ++ [.ident "return"] ++
    declaration.result.tokens ++ [.symbol ';', .symbol '}']

def InfixLeaf.tokens : InfixLeaf → List Token
  | .plain statement => statement.tokens
  | .letInfix identifier type op left right =>
      [.ident "let", .ident identifier, .symbol ':'] ++ type.tokens ++ [.symbol '='] ++
        left.tokens ++ [op.token] ++ right.tokens ++ [.symbol ';']
  | .assignInfix identifier op left right =>
      [.ident identifier, .symbol '='] ++ left.tokens ++ [op.token] ++ right.tokens ++
        [.symbol ';']

def InfixLeaf.listTokens : List InfixLeaf → List Token
  | [] => []
  | statement :: rest => statement.tokens ++ InfixLeaf.listTokens rest

def InfixStmt.tokens : InfixStmt → List Token
  | .leaf statement => statement.tokens
  | .matchPair scrutinee first second body =>
      [.ident "match", .symbol '('] ++ scrutinee.tokens ++
        [.symbol ')', .symbol '{', .ident "case", .symbol '(', .ident first, .symbol ',',
          .ident second, .symbol ')', .symbol '{'] ++
        InfixLeaf.listTokens body ++ [.symbol '}', .symbol '}']
  | .matchSum scrutinee left leftBody right rightBody =>
      [.ident "match", .symbol '('] ++ scrutinee.tokens ++
        [.symbol ')', .symbol '{', .ident "case", .ident "inl", .symbol '(', .ident left,
          .symbol ')', .symbol '{'] ++
        InfixLeaf.listTokens leftBody ++
        [.symbol '}', .ident "case", .ident "inr", .symbol '(', .ident right, .symbol ')',
          .symbol '{'] ++
        InfixLeaf.listTokens rightBody ++ [.symbol '}', .symbol '}']

def InfixStmt.listTokens : List InfixStmt → List Token
  | [] => []
  | statement :: rest => statement.tokens ++ InfixStmt.listTokens rest

def GenericFile.tokens (file : GenericFile) : List Token :=
  importTokens ++ aliasImportTokens file.opcodeAliases ++
    file.generics.flatMap GenericDecl.tokens ++ file.functions.flatMap FunctionDecl.tokens ++
    [.ident "contract", .ident file.contract, .symbol '{', .ident "function",
      .ident file.method.name, .symbol '('] ++ parameterTokens file.method.parameters ++
    signatureTokens ++ InfixStmt.listTokens file.method.body ++ [.ident "return"] ++
    file.method.result.tokens ++ [.symbol ';', .symbol '}', .symbol '}']

/-! ### Parser -/

/-- A type of the fragment, otherwise a type parameter. -/
def parseTypeRef (tokens : List Token) : Option (TypeRef × List Token) :=
  match parseLocalType tokens with
  | some (type, rest) => some (.concrete type, rest)
  | none => (parseName tokens).map fun (name, rest) => (.param name, rest)

/-- Type parameter names separated by commas, up to the closing `>`. -/
def parseTypeParameterList : Nat → List Token → Option (List String × List Token)
  | 0, _ => none
  | fuel + 1, tokens => do
      let (name, rest) ← parseName tokens
      if rest.head? = some (.symbol ',') then do
        let (names, rest) ← parseTypeParameterList fuel rest.tail
        some (name :: names, rest)
      else some ([name], rest)

/-- `name: type` parameters separated by commas, up to the closing
parenthesis, where a type may be a type parameter. -/
def parseGenericParameterList :
    Nat → List Token → Option (List (String × TypeRef) × List Token)
  | 0, _ => none
  | fuel + 1, tokens => do
      let (parameter, rest) ← parseName tokens
      let rest ← expectTokens [.symbol ':'] rest
      let (type, rest) ← parseTypeRef rest
      if rest.head? = some (.symbol ',') then do
        let (parameters, rest) ← parseGenericParameterList fuel rest.tail
        some ((parameter, type) :: parameters, rest)
      else some ([(parameter, type)], rest)

def parseGenericParameters (tokens : List Token) :
    Option (List (String × TypeRef) × List Token) :=
  if tokens.head? = some (.symbol ')') then some ([], tokens)
  else parseGenericParameterList (tokens.length + 1) tokens

/-- The local a guard tests, when the tokens start with `if ( name ) { return`. -/
def guardName? (tokens : List Token) : Option String :=
  match (tokens[2]? : Option Token) with
  | some (Token.ident name) => if tokens.take 6 = guardTokens name then some name else none
  | _ => none

/-- Generic function body statements up to `return`: a guard where the tokens
start like one, otherwise a loop-free statement. -/
def parseGuardStmts : Nat → List Token → Option (List GuardStmt × List Token)
  | 0, _ => none
  | fuel + 1, tokens =>
      if blockEnds tokens then some ([], tokens)
      else match guardName? tokens with
        | some name => do
            let (value, rest) ← parseExpr fuel (tokens.drop 6)
            let rest ← expectTokens [.symbol ';', .symbol '}'] rest
            let (statements, rest) ← parseGuardStmts fuel rest
            some (.guard name value :: statements, rest)
        | none => do
            let (statement, rest) ← parseStmt fuel tokens
            let (statements, rest) ← parseGuardStmts fuel rest
            some (.plain statement :: statements, rest)

def parseGenericDecl (fuel : Nat) (tokens : List Token) : Option (GenericDecl × List Token) := do
  let rest ← expectTokens [.ident "function"] tokens
  let (name, rest) ← parseName rest
  let rest ← expectTokens [.symbol '<'] rest
  let (typeParameters, rest) ← parseTypeParameterList (rest.length + 1) rest
  let rest ← expectTokens [.symbol '>', .symbol '('] rest
  let (parameters, rest) ← parseGenericParameters rest
  let rest ← expectTokens [.symbol ')', .ident "returns", .symbol '('] rest
  let (resultType, rest) ← parseTypeRef rest
  let rest ← expectTokens [.symbol ')', .symbol '{'] rest
  let (body, rest) ← parseGuardStmts fuel rest
  let rest ← expectTokens [.ident "return"] rest
  let (result, rest) ← parseExpr fuel rest
  let rest ← expectTokens [.symbol ';', .symbol '}'] rest
  some (⟨name, typeParameters, parameters, resultType, body, result⟩, rest)

/-- Whether the tokens start a generic function: `function name <`. -/
def startsGeneric (tokens : List Token) : Bool :=
  decide (tokens.head? = some (.ident "function")) &&
    decide ((tokens.drop 2).head? = some (.symbol '<'))

/-- Generic functions up to the first ordinary one; `count` bounds their
number. -/
def parseGenerics : Nat → Nat → List Token → Option (List GenericDecl × List Token)
  | 0, _, _ => none
  | count + 1, fuel, tokens =>
      if startsGeneric tokens then do
        let (declaration, rest) ← parseGenericDecl fuel tokens
        let (declarations, rest) ← parseGenerics count fuel rest
        some (declaration :: declarations, rest)
      else some ([], tokens)

/-- The end of `let x: T = left` or `x = left`: `;`, or an infix operator,
its right operand and `;`. -/
def parseInfixTail (fuel : Nat) : List Token → Option (Option (BinaryOp × Expr) × List Token)
  | .symbol ';' :: rest => some (none, rest)
  | next :: rest => do
      let op ← parseBinaryOp? next
      let (right, rest) ← parseExpr fuel rest
      let rest ← expectTokens [.symbol ';'] rest
      some (some (op, right), rest)
  | [] => none

/-- A leaf: a `let` or an assignment, either of which may end with an infix
operation, or another loop-free statement. -/
def parseInfixLeaf : Nat → List Token → Option (InfixLeaf × List Token)
  | 0, _ => none
  | fuel + 1, tokens =>
      match tokens with
      | .ident text :: rest =>
          if text = "let" then do
            let (identifier, rest) ← parseName rest
            let rest ← expectTokens [.symbol ':'] rest
            let (type, rest) ← parseLocalType rest
            let rest ← expectTokens [.symbol '='] rest
            let (left, rest) ← parseExpr fuel rest
            let (tail, rest) ← parseInfixTail fuel rest
            match tail with
            | none => some (.plain (.letDecl identifier type left), rest)
            | some (op, right) => some (.letInfix identifier type op left right, rest)
          else if isReserved text then do
            let (statement, rest) ← parseStmt (fuel + 1) tokens
            some (.plain statement, rest)
          else do
            let rest ← expectTokens [.symbol '='] rest
            let (left, rest) ← parseExpr fuel rest
            let (tail, rest) ← parseInfixTail fuel rest
            match tail with
            | none => some (.plain (.assign text left), rest)
            | some (op, right) => some (.assignInfix text op left right, rest)
      | _ => none

def parseInfixLeaves : Nat → List Token → Option (List InfixLeaf × List Token)
  | 0, _ => none
  | fuel + 1, tokens =>
      if blockEnds tokens then some ([], tokens)
      else do
        let (statement, rest) ← parseInfixLeaf fuel tokens
        let (statements, rest) ← parseInfixLeaves fuel rest
        some (statement :: statements, rest)

/-- A `match` whose cases run leaves, otherwise a leaf. -/
def parseInfixStmt : Nat → List Token → Option (InfixStmt × List Token)
  | 0, _ => none
  | fuel + 1, tokens =>
      if tokens.head? = some (.ident "match") then do
        let rest ← expectTokens [.ident "match", .symbol '('] tokens
        let (scrutinee, rest) ← parseExpr fuel rest
        let rest ← expectTokens [.symbol ')', .symbol '{', .ident "case"] rest
        if rest.head? = some (.symbol '(') then do
          let (first, rest) ← parseName rest.tail
          let rest ← expectTokens [.symbol ','] rest
          let (second, rest) ← parseName rest
          let rest ← expectTokens [.symbol ')', .symbol '{'] rest
          let (body, rest) ← parseInfixLeaves fuel rest
          let rest ← expectTokens [.symbol '}', .symbol '}'] rest
          some (.matchPair scrutinee first second body, rest)
        else do
          let rest ← expectTokens [.ident "inl", .symbol '('] rest
          let (left, rest) ← parseName rest
          let rest ← expectTokens [.symbol ')', .symbol '{'] rest
          let (leftBody, rest) ← parseInfixLeaves fuel rest
          let rest ← expectTokens
            [.symbol '}', .ident "case", .ident "inr", .symbol '('] rest
          let (right, rest) ← parseName rest
          let rest ← expectTokens [.symbol ')', .symbol '{'] rest
          let (rightBody, rest) ← parseInfixLeaves fuel rest
          let rest ← expectTokens [.symbol '}', .symbol '}'] rest
          some (.matchSum scrutinee left leftBody right rightBody, rest)
      else do
        let (statement, rest) ← parseInfixLeaf (fuel + 1) tokens
        some (.leaf statement, rest)

def parseInfixStmts : Nat → List Token → Option (List InfixStmt × List Token)
  | 0, _ => none
  | fuel + 1, tokens =>
      if blockEnds tokens then some ([], tokens)
      else do
        let (statement, rest) ← parseInfixStmt fuel tokens
        let (statements, rest) ← parseInfixStmts fuel rest
        some (statement :: statements, rest)

/-- `parseFileWith` with generic functions before the ordinary ones and an
infix method body. -/
def parseGenericFileWith (fuel : Nat) (tokens : List Token) : Option GenericFile := do
  let rest ← expectTokens importTokens tokens
  let (opcodeAliases, rest) ← parseAliasImport rest
  let (generics, rest) ← parseGenerics (tokens.length + 1) fuel rest
  let (functions, rest) ← parseFunctions (tokens.length + 1) fuel rest
  let rest ← expectTokens [.ident "contract"] rest
  let (contract, rest) ← parseName rest
  let rest ← expectTokens [.symbol '{', .ident "function"] rest
  let (method, rest) ← parseName rest
  let rest ← expectTokens [.symbol '('] rest
  let (parameters, rest) ← parseParameters rest
  let rest ← expectTokens signatureTokens rest
  let (body, rest) ← parseInfixStmts fuel rest
  let rest ← expectTokens [.ident "return"] rest
  let (result, rest) ← parseExpr fuel rest
  let rest ← expectTokens [.symbol ';', .symbol '}', .symbol '}'] rest
  if rest = [] then
    some ⟨opcodeAliases, generics, functions, contract, ⟨method, parameters, body, result⟩⟩
  else none

/-- Parse a complete token stream; one more than its length bounds nesting. -/
def parseGenericFile (tokens : List Token) : Option GenericFile :=
  parseGenericFileWith (tokens.length + 1) tokens

def parseGenericSource (source : String) : Option GenericFile :=
  (lex source.toList).bind parseGenericFile

/-- The returned ABI word of calling `method` on the contract written in
`source`, read as a generic program. -/
def genericSourceCall (source : String) (method : String) (arguments : List Nat) :
    Option Nat :=
  (parseGenericSource source).bind fun file => file.call method arguments

/-! ### Sizes and names -/

def GuardStmt.size : GuardStmt → Nat
  | .plain statement => statement.size
  | .guard _ value => value.size + 1

def GuardStmt.listSize : List GuardStmt → Nat
  | [] => 0
  | statement :: rest => statement.size + GuardStmt.listSize rest + 1

def InfixLeaf.size : InfixLeaf → Nat
  | .plain statement => statement.size
  | .letInfix _ _ _ left right => left.size + right.size + 1
  | .assignInfix _ _ left right => left.size + right.size + 1

def InfixLeaf.listSize : List InfixLeaf → Nat
  | [] => 0
  | statement :: rest => statement.size + InfixLeaf.listSize rest + 1

def InfixStmt.size : InfixStmt → Nat
  | .leaf statement => statement.size
  | .matchPair scrutinee _ _ body => scrutinee.size + InfixLeaf.listSize body + 1
  | .matchSum scrutinee _ leftBody _ rightBody =>
      scrutinee.size + InfixLeaf.listSize leftBody + InfixLeaf.listSize rightBody + 1

def InfixStmt.listSize : List InfixStmt → Nat
  | [] => 0
  | statement :: rest => statement.size + InfixStmt.listSize rest + 1

def TypeRef.NamesOk (type : TypeRef) : Prop :=
  ∀ name ∈ type.identifiers, isReserved name = false

def GuardStmt.ListNamesOk (statements : List GuardStmt) : Prop :=
  ∀ name ∈ GuardStmt.listIdentifiers statements, isReserved name = false

/-- Every name of a generic function is a non-reserved word, and it has a type
parameter. -/
def GenericDecl.NamesOk (declaration : GenericDecl) : Prop :=
  (∀ name ∈ declaration.identifiers, isReserved name = false) ∧
    declaration.typeParameters ≠ []

def InfixLeaf.NamesOk (statement : InfixLeaf) : Prop :=
  ∀ name ∈ statement.identifiers, isReserved name = false

def InfixLeaf.ListNamesOk (statements : List InfixLeaf) : Prop :=
  ∀ name ∈ InfixLeaf.listIdentifiers statements, isReserved name = false

def InfixStmt.ListNamesOk (statements : List InfixStmt) : Prop :=
  ∀ name ∈ InfixStmt.listIdentifiers statements, isReserved name = false

/-- The parser reads a `match` at the top of the method body as a `match` of
leaves, so a leaf is never a `match`. -/
def InfixStmt.Canonical : InfixStmt → Prop
  | .leaf (.plain (.matchPair _ _ _ _)) => False
  | .leaf (.plain (.matchSum _ _ _ _ _)) => False
  | _ => True

def GenericFile.NamesOk (file : GenericFile) : Prop :=
  (∀ declaration ∈ file.generics, declaration.NamesOk) ∧
    (∀ function ∈ file.functions, function.NamesOk) ∧
    isReserved file.contract = false ∧ isReserved file.method.name = false ∧
    (∀ parameter ∈ file.method.parameters, isReserved parameter = false) ∧
    InfixStmt.ListNamesOk file.method.body ∧ (∀ statement ∈ file.method.body,
      statement.Canonical) ∧ file.method.result.NamesOk

/-! ### Parser round trip: signatures -/

theorem TypeRef.parse_tokens (type : TypeRef) (names : type.NamesOk) (rest : List Token)
    (notLess : rest.head? ≠ some (.symbol '<')) :
    parseTypeRef (type.tokens ++ rest) = some (type, rest) := by
  cases type with
  | concrete type => simp [parseTypeRef, TypeRef.tokens, LocalType.parse_tokens]
  | param name =>
      have notReserved : isReserved name = false := names name (by simp [TypeRef.identifiers])
      have notWord : name ≠ "word" := by
        intro same
        subst same
        simp [isReserved, reservedWords] at notReserved
      have notBool : name ≠ "bool" := by
        intro same
        subst same
        simp [isReserved, reservedWords] at notReserved
      have notLocal : parseLocalType (.ident name :: rest) = none := by
        by_cases sum : name = "sum"
        · subst sum
          cases rest with
          | nil => simp [parseLocalType, expectTokens]
          | cons first more =>
              have different : Token.symbol '<' ≠ first := fun same => notLess (by simp [same])
              simp [parseLocalType, expectTokens, different]
        · simp [parseLocalType, notWord, notBool, sum]
      simp [parseTypeRef, TypeRef.tokens, notLocal, parseName_cons notReserved]

theorem parseTypeParameterList_tokens : ∀ (names : List String) (fuel : Nat) (rest : List Token),
    names ≠ [] → (∀ name ∈ names, isReserved name = false) → names.length ≤ fuel →
    rest.head? = some (.symbol '>') →
    parseTypeParameterList fuel (typeParameterTokens names ++ rest) = some (names, rest)
  | [], _, _, nonempty, _, _, _ => absurd rfl nonempty
  | [name], fuel + 1, rest, _, names, _, closing => by
      have notReserved := names name (by simp)
      cases rest with
      | nil => simp at closing
      | cons first tail =>
          simp only [List.head?_cons, Option.some.injEq] at closing
          subst closing
          simp [typeParameterTokens, parseTypeParameterList, parseName_cons notReserved]
  | name :: next :: more, fuel + 1, rest, _, names, enough, closing => by
      have notReserved := names name (by simp)
      have tailParse := parseTypeParameterList_tokens (next :: more) fuel rest (by simp)
        (fun other mem => names other (List.mem_cons_of_mem _ mem))
        (by simp only [List.length_cons] at enough ⊢; omega) closing
      simp only [typeParameterTokens, List.cons_append, List.nil_append]
      simp [parseTypeParameterList, parseName_cons notReserved, tailParse]
  | _ :: _, 0, _, _, _, enough, _ => absurd enough (by simp)

theorem typeParameterTokens_length : (names : List String) →
    names.length ≤ (typeParameterTokens names).length
  | [] => Nat.le_refl _
  | [_] => by simp [typeParameterTokens]
  | _ :: next :: more => by
      have := typeParameterTokens_length (next :: more)
      simp only [typeParameterTokens, List.length_append, List.length_cons,
        List.length_nil] at this ⊢
      omega

theorem parseGenericParameterList_tokens :
    ∀ (parameters : List (String × TypeRef)) (fuel : Nat) (rest : List Token),
    parameters ≠ [] →
    (∀ parameter ∈ parameters, isReserved parameter.1 = false ∧ parameter.2.NamesOk) →
    parameters.length ≤ fuel → rest.head? = some (.symbol ')') →
    parseGenericParameterList fuel (genericParameterTokens parameters ++ rest) =
      some (parameters, rest)
  | [], _, _, nonempty, _, _, _ => absurd rfl nonempty
  | [parameter], fuel + 1, rest, _, names, _, closing => by
      obtain ⟨notReserved, typeNames⟩ := names parameter (by simp)
      have typeParse := TypeRef.parse_tokens parameter.2 typeNames rest
        (by rw [closing]; simp)
      cases rest with
      | nil => simp at closing
      | cons first tail =>
          simp only [List.head?_cons, Option.some.injEq] at closing
          subst closing
          simp [genericParameterTokens, parseGenericParameterList, parseName_cons notReserved,
            expectTokens, typeParse]
  | parameter :: next :: more, fuel + 1, rest, _, names, enough, closing => by
      obtain ⟨notReserved, typeNames⟩ := names parameter (by simp)
      have tailParse := parseGenericParameterList_tokens (next :: more) fuel rest (by simp)
        (fun other mem => names other (List.mem_cons_of_mem _ mem))
        (by simp only [List.length_cons] at enough ⊢; omega) closing
      have typeParse := TypeRef.parse_tokens parameter.2 typeNames
        (.symbol ',' :: (genericParameterTokens (next :: more) ++ rest)) (by simp)
      simp only [genericParameterTokens, List.cons_append, List.nil_append, List.append_assoc]
        at typeParse ⊢
      simp [parseGenericParameterList, parseName_cons notReserved, expectTokens, typeParse,
        tailParse]
  | _ :: _, 0, _, _, _, enough, _ => absurd enough (by simp)

theorem genericParameterTokens_length : (parameters : List (String × TypeRef)) →
    parameters.length ≤ (genericParameterTokens parameters).length
  | [] => Nat.le_refl _
  | [_] => by simp [genericParameterTokens]
  | _ :: next :: more => by
      have := genericParameterTokens_length (next :: more)
      simp only [genericParameterTokens, List.length_append, List.length_cons,
        List.length_nil] at this ⊢
      omega

theorem parseGenericParameters_tokens (parameters : List (String × TypeRef))
    (rest : List Token)
    (names : ∀ parameter ∈ parameters, isReserved parameter.1 = false ∧ parameter.2.NamesOk)
    (closing : rest.head? = some (.symbol ')')) :
    parseGenericParameters (genericParameterTokens parameters ++ rest) =
      some (parameters, rest) := by
  cases parameters with
  | nil => simp [genericParameterTokens, parseGenericParameters, closing]
  | cons parameter more =>
      have notClosing : (genericParameterTokens (parameter :: more) ++ rest).head? ≠
          some (.symbol ')') := by
        cases more <;> simp [genericParameterTokens]
      rw [parseGenericParameters, if_neg notClosing]
      have := genericParameterTokens_length (parameter :: more)
      exact parseGenericParameterList_tokens _ _ rest (by simp) names
        (by simp only [List.length_append]; omega) closing

/-! ### Parser round trip: generic functions -/

theorem guardName?_guardTokens (name : String) (rest : List Token) :
    guardName? (guardTokens name ++ rest) = some name := by
  simp [guardName?, guardTokens]

theorem guardName?_eq_some {tokens : List Token} {name : String}
    (found : guardName? tokens = some name) : tokens = guardTokens name ++ tokens.drop 6 := by
  unfold guardName? at found
  split at found
  · split at found
    · rename_i prefixEq
      simp only [Option.some.injEq] at found
      subst found
      rw [← prefixEq, List.take_append_drop]
    · cases found
  · cases found

/-- A statement of the fragment never starts with `return`. -/
theorem Stmt.tokens_ne_return (statement : Stmt) (names : statement.NamesOk)
    (rest more : List Token) : statement.tokens ++ rest ≠ .ident "return" :: more := by
  intro same
  have ends := Stmt.blockEnds_tokens statement names rest
  rw [same] at ends
  simp [blockEnds] at ends

theorem Stmt.listTokens_ne_return (statements : List Stmt) (names : Stmt.ListNamesOk statements)
    (rest more : List Token) (closing : rest.head? = some (.symbol '}')) :
    Stmt.listTokens statements ++ rest ≠ .ident "return" :: more := by
  cases statements with
  | nil =>
      intro same
      simp only [Stmt.listTokens, List.nil_append] at same
      rw [same] at closing
      simp at closing
  | cons statement tail =>
      simp only [Stmt.listTokens, List.append_assoc]
      exact Stmt.tokens_ne_return statement
        (fun name mem => names name (by simp [Stmt.listIdentifiers, mem])) _ more

/-- No statement of the fragment starts like a guard. -/
theorem Stmt.guardName?_tokens (statement : Stmt) (names : statement.NamesOk)
    (rest : List Token) : guardName? (statement.tokens ++ rest) = none := by
  cases found : guardName? (statement.tokens ++ rest) with
  | none => rfl
  | some name =>
      have shape := guardName?_eq_some found
      exfalso
      cases statement with
      | letDecl identifier type initializer =>
          simp [Stmt.tokens, guardTokens] at shape
      | assign identifier value =>
          have notIf := (not_reserved_ne (names identifier (by simp [Stmt.identifiers]))).2.1
          simp [Stmt.tokens, guardTokens, notIf] at shape
      | ifElse condition thenBlock elseBlock =>
          have thenNames : Stmt.ListNamesOk thenBlock :=
            fun name mem => names name (by simp [Stmt.identifiers, mem])
          have noReturn := Stmt.listTokens_ne_return thenBlock thenNames
            (.symbol '}' :: .ident "else" :: .symbol '{' :: (Stmt.listTokens elseBlock ++
              .symbol '}' :: rest))
          cases condition <;>
            simp [Stmt.tokens, Expr.tokens, guardTokens] at shape <;>
            exact noReturn _ (by simp) shape.2
      | matchPair scrutinee first second body =>
          simp [Stmt.tokens, guardTokens] at shape
      | matchSum scrutinee left leftBody right rightBody =>
          simp [Stmt.tokens, guardTokens] at shape

theorem parseGuardStmts_tokens : ∀ (statements : List GuardStmt) (fuel : Nat)
    (rest : List Token), GuardStmt.ListNamesOk statements →
    GuardStmt.listSize statements < fuel → blockEnds rest = true →
    parseGuardStmts fuel (GuardStmt.listTokens statements ++ rest) = some (statements, rest)
  | [], fuel + 1, rest, _, _, ends => by simp [GuardStmt.listTokens, parseGuardStmts, ends]
  | .plain statement :: tail, fuel + 1, rest, names, enough, ends => by
      have statementNames : statement.NamesOk := fun name mem =>
        names name (by simp [GuardStmt.listIdentifiers, GuardStmt.identifiers, mem])
      have statementParse := (parseStmt_tokens_all fuel).1 statement
        (GuardStmt.listTokens tail ++ rest) statementNames
        (by simp only [GuardStmt.listSize, GuardStmt.size] at enough; omega)
      have tailParse := parseGuardStmts_tokens tail fuel rest
        (fun name mem => names name (by simp [GuardStmt.listIdentifiers, mem]))
        (by simp only [GuardStmt.listSize] at enough; omega) ends
      simp only [GuardStmt.listTokens, GuardStmt.tokens, List.append_assoc]
      rw [parseGuardStmts, if_neg (by rw [Stmt.blockEnds_tokens statement statementNames]; simp),
        Stmt.guardName?_tokens statement statementNames]
      simp [statementParse, tailParse]
  | .guard condition value :: tail, fuel + 1, rest, names, enough, ends => by
      have valueParse := parseExpr_tokens value fuel
        ([.symbol ';', .symbol '}'] ++ (GuardStmt.listTokens tail ++ rest))
        (fun name mem => names name (by
          simp [GuardStmt.listIdentifiers, GuardStmt.identifiers, mem]))
        (by simp only [GuardStmt.listSize, GuardStmt.size] at enough; omega) (by simp)
      have tailParse := parseGuardStmts_tokens tail fuel rest
        (fun name mem => names name (by simp [GuardStmt.listIdentifiers, mem]))
        (by simp only [GuardStmt.listSize] at enough; omega) ends
      simp only [GuardStmt.listTokens, GuardStmt.tokens, List.append_assoc]
      rw [parseGuardStmts, if_neg (by simp [guardTokens, blockEnds]),
        guardName?_guardTokens]
      simp only [List.cons_append, List.nil_append] at valueParse
      simp [guardTokens, valueParse, expectTokens, tailParse]
  | _, 0, _, _, enough, _ => absurd enough (Nat.not_lt_zero _)

theorem parseGenericDecl_tokens (declaration : GenericDecl) (names : declaration.NamesOk)
    (fuel : Nat) (bodyFuel : GuardStmt.listSize declaration.body < fuel)
    (resultFuel : declaration.result.size < fuel) (rest : List Token) :
    parseGenericDecl fuel (declaration.tokens ++ rest) = some (declaration, rest) := by
  obtain ⟨allNames, nonempty⟩ := names
  have nameOk : isReserved declaration.name = false :=
    allNames _ (by simp [GenericDecl.identifiers])
  have typeParametersOk : ∀ name ∈ declaration.typeParameters, isReserved name = false :=
    fun name mem => allNames name (by simp [GenericDecl.identifiers, mem])
  have parametersOk : ∀ parameter ∈ declaration.parameters,
      isReserved parameter.1 = false ∧ parameter.2.NamesOk := by
    have inner : ∀ (parameters : List (String × TypeRef)),
        (∀ name ∈ genericParameterIdentifiers parameters, isReserved name = false) →
        ∀ parameter ∈ parameters, isReserved parameter.1 = false ∧ parameter.2.NamesOk := by
      intro parameters
      induction parameters with
      | nil => intro _ _ absent; cases absent
      | cons first more ih =>
          intro all parameter mem
          rcases List.mem_cons.mp mem with same | mem
          · subst same
            exact ⟨all _ (by simp [genericParameterIdentifiers]),
              fun name found => all name (by simp [genericParameterIdentifiers, found])⟩
          · exact ih (fun name found => all name (by
              simp [genericParameterIdentifiers, found])) parameter mem
    exact inner declaration.parameters
      (fun name mem => allNames name (by simp [GenericDecl.identifiers, mem]))
  have resultTypeOk : declaration.resultType.NamesOk :=
    fun name mem => allNames name (by simp [GenericDecl.identifiers, mem])
  have bodyOk : GuardStmt.ListNamesOk declaration.body :=
    fun name mem => allNames name (by simp [GenericDecl.identifiers, mem])
  have resultOk : declaration.result.NamesOk :=
    fun name mem => allNames name (by simp [GenericDecl.identifiers, mem])
  have bodyParse := parseGuardStmts_tokens declaration.body fuel
    (.ident "return" :: (declaration.result.tokens ++ (.symbol ';' :: .symbol '}' :: rest)))
    bodyOk bodyFuel rfl
  have resultParse := parseExpr_tokens declaration.result fuel
    (.symbol ';' :: .symbol '}' :: rest) resultOk resultFuel (by simp)
  have resultTypeParse := TypeRef.parse_tokens declaration.resultType resultTypeOk
    (.symbol ')' :: .symbol '{' :: (GuardStmt.listTokens declaration.body ++
      (.ident "return" :: (declaration.result.tokens ++ (.symbol ';' :: .symbol '}' :: rest)))))
    (by simp)
  have parametersParse := parseGenericParameters_tokens declaration.parameters
    (.symbol ')' :: .ident "returns" :: .symbol '(' :: (declaration.resultType.tokens ++
      (.symbol ')' :: .symbol '{' :: (GuardStmt.listTokens declaration.body ++
        (.ident "return" :: (declaration.result.tokens ++
          (.symbol ';' :: .symbol '}' :: rest)))))))
    parametersOk rfl
  have typeParametersParse : ∀ bound, declaration.typeParameters.length ≤ bound →
      parseTypeParameterList bound (typeParameterTokens declaration.typeParameters ++
        (.symbol '>' :: .symbol '(' :: (genericParameterTokens declaration.parameters ++
          (.symbol ')' :: .ident "returns" :: .symbol '(' :: (declaration.resultType.tokens ++
            (.symbol ')' :: .symbol '{' :: (GuardStmt.listTokens declaration.body ++
              (.ident "return" :: (declaration.result.tokens ++
                (.symbol ';' :: .symbol '}' :: rest)))))))))) =
        some (declaration.typeParameters, .symbol '>' :: .symbol '(' ::
          (genericParameterTokens declaration.parameters ++
            (.symbol ')' :: .ident "returns" :: .symbol '(' :: (declaration.resultType.tokens ++
              (.symbol ')' :: .symbol '{' :: (GuardStmt.listTokens declaration.body ++
                (.ident "return" :: (declaration.result.tokens ++
                  (.symbol ';' :: .symbol '}' :: rest))))))))) :=
    fun bound enough => parseTypeParameterList_tokens _ bound _ nonempty typeParametersOk
      enough rfl
  have typeLength := typeParameterTokens_length declaration.typeParameters
  simp only [parseGenericDecl, GenericDecl.tokens, List.append_assoc, List.cons_append,
    List.nil_append]
  simp only [expectTokens, if_true, parseName_cons nameOk, Option.bind_eq_bind,
    Option.bind_some]
  rw [typeParametersParse _ (by simp only [List.length_append, List.length_cons]; omega)]
  simp [expectTokens, parametersParse, resultTypeParse, bodyParse, resultParse]

theorem startsGeneric_tokens (declaration : GenericDecl) (rest : List Token) :
    startsGeneric (declaration.tokens ++ rest) = true := by
  simp [startsGeneric, GenericDecl.tokens]

theorem parseGenerics_tokens : ∀ (generics : List GenericDecl) (count fuel : Nat)
    (rest : List Token),
    (∀ declaration ∈ generics, declaration.NamesOk ∧
      GuardStmt.listSize declaration.body < fuel ∧ declaration.result.size < fuel) →
    generics.length < count → startsGeneric rest = false →
    parseGenerics count fuel (generics.flatMap GenericDecl.tokens ++ rest) =
      some (generics, rest)
  | [], count + 1, fuel, rest, _, _, next => by
      simp [parseGenerics, next]
  | declaration :: more, count + 1, fuel, rest, ok, enough, next => by
      obtain ⟨names, bodyFuel, resultFuel⟩ := ok declaration (by simp)
      have tailParse := parseGenerics_tokens more count fuel rest
        (fun other mem => ok other (List.mem_cons_of_mem _ mem))
        (by simp only [List.length_cons] at enough; omega) next
      have declarationParse := parseGenericDecl_tokens declaration names fuel bodyFuel
        resultFuel (more.flatMap GenericDecl.tokens ++ rest)
      simp only [List.flatMap_cons, List.append_assoc]
      rw [parseGenerics, if_pos (startsGeneric_tokens declaration _)]
      simp [declarationParse, tailParse]
  | _, 0, _, _, _, enough, _ => absurd enough (Nat.not_lt_zero _)

/-! ### Parser round trip: infix statements -/

theorem parseInfixTail_end (fuel : Nat) (rest : List Token) :
    parseInfixTail fuel (.symbol ';' :: rest) = some (none, rest) := by
  simp [parseInfixTail]

theorem parseInfixTail_infix (op : BinaryOp) (right : Expr) (fuel : Nat)
    (names : right.NamesOk) (enough : right.size < fuel) (rest : List Token) :
    parseInfixTail fuel (op.token :: (right.tokens ++ .symbol ';' :: rest)) =
      some (some (op, right), rest) := by
  have rightParse := parseExpr_tokens right fuel (.symbol ';' :: rest) names enough (by simp)
  cases op <;> simp [parseInfixTail, BinaryOp.token, parseBinaryOp?, rightParse, expectTokens]

theorem parseInfixLeaf_reserved {fuel : Nat} {text : String} {more : List Token}
    (reserved : isReserved text = true) (notLet : text ≠ "let") :
    parseInfixLeaf (fuel + 1) (.ident text :: more) =
      (parseStmt (fuel + 1) (.ident text :: more)).map
        fun parsed => (.plain parsed.1, parsed.2) := by
  simp only [parseInfixLeaf, notLet, if_false, reserved, if_true]
  cases parseStmt (fuel + 1) (.ident text :: more) <;> rfl

theorem parseInfixLeaf_tokens (statement : InfixLeaf) (names : statement.NamesOk) (fuel : Nat)
    (enough : statement.size < fuel) (rest : List Token) :
    parseInfixLeaf fuel (statement.tokens ++ rest) = some (statement, rest) := by
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
  cases statement with
  | plain statement =>
      have statementNames : statement.NamesOk := names
      have statementParse := (parseStmt_tokens_all (fuel + 1)).1 statement rest statementNames
        (by simpa [InfixLeaf.size] using enough)
      cases statement with
      | letDecl identifier type initializer =>
          have notReserved : isReserved identifier = false :=
            names identifier (by simp [InfixLeaf.identifiers, Stmt.identifiers])
          have initializerParse := parseExpr_tokens initializer fuel (.symbol ';' :: rest)
            (fun name mem => names name (by
              simp [InfixLeaf.identifiers, Stmt.identifiers, mem]))
            (by simp only [InfixLeaf.size, Stmt.size] at enough; omega) (by simp)
          simp only [InfixLeaf.tokens, Stmt.tokens, List.append_assoc, List.cons_append,
            List.nil_append]
          simp [parseInfixLeaf, parseName_cons notReserved, expectTokens,
            LocalType.parse_tokens, initializerParse, parseInfixTail_end]
      | assign identifier value =>
          have notReserved : isReserved identifier = false :=
            names identifier (by simp [InfixLeaf.identifiers, Stmt.identifiers])
          have notLet := (not_reserved_ne notReserved).1
          have valueParse := parseExpr_tokens value fuel (.symbol ';' :: rest)
            (fun name mem => names name (by
              simp [InfixLeaf.identifiers, Stmt.identifiers, mem]))
            (by simp only [InfixLeaf.size, Stmt.size] at enough; omega) (by simp)
          simp only [InfixLeaf.tokens, Stmt.tokens, List.append_assoc, List.cons_append,
            List.nil_append]
          simp [parseInfixLeaf, notLet, notReserved, expectTokens, valueParse,
            parseInfixTail_end]
      | ifElse condition thenBlock elseBlock =>
          obtain ⟨more, shape⟩ : ∃ more,
              (Stmt.ifElse condition thenBlock elseBlock).tokens ++ rest = .ident "if" :: more :=
            ⟨_, rfl⟩
          show parseInfixLeaf (fuel + 1)
            ((Stmt.ifElse condition thenBlock elseBlock).tokens ++ rest) = _
          rw [shape, parseInfixLeaf_reserved (by decide) (by decide), ← shape, statementParse]
          rfl
      | matchPair scrutinee first second body =>
          obtain ⟨more, shape⟩ : ∃ more,
              (Stmt.matchPair scrutinee first second body).tokens ++ rest =
                .ident "match" :: more := ⟨_, rfl⟩
          show parseInfixLeaf (fuel + 1)
            ((Stmt.matchPair scrutinee first second body).tokens ++ rest) = _
          rw [shape, parseInfixLeaf_reserved (by decide) (by decide), ← shape, statementParse]
          rfl
      | matchSum scrutinee left leftBody right rightBody =>
          obtain ⟨more, shape⟩ : ∃ more,
              (Stmt.matchSum scrutinee left leftBody right rightBody).tokens ++ rest =
                .ident "match" :: more := ⟨_, rfl⟩
          show parseInfixLeaf (fuel + 1)
            ((Stmt.matchSum scrutinee left leftBody right rightBody).tokens ++ rest) = _
          rw [shape, parseInfixLeaf_reserved (by decide) (by decide), ← shape, statementParse]
          rfl
  | letInfix identifier type op left right =>
      have notReserved : isReserved identifier = false :=
        names identifier (by simp [InfixLeaf.identifiers])
      have leftParse := parseExpr_tokens left fuel
        (op.token :: (right.tokens ++ .symbol ';' :: rest))
        (fun name mem => names name (by simp [InfixLeaf.identifiers, mem]))
        (by simp only [InfixLeaf.size] at enough; omega) (by simp [BinaryOp.token_ne_open])
      have tailParse := parseInfixTail_infix op right fuel
        (fun name mem => names name (by simp [InfixLeaf.identifiers, mem]))
        (by simp only [InfixLeaf.size] at enough; omega) rest
      simp only [InfixLeaf.tokens, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseInfixLeaf, parseName_cons notReserved, expectTokens, LocalType.parse_tokens,
        leftParse, tailParse]
  | assignInfix identifier op left right =>
      have notReserved : isReserved identifier = false :=
        names identifier (by simp [InfixLeaf.identifiers])
      have notLet := (not_reserved_ne notReserved).1
      have leftParse := parseExpr_tokens left fuel
        (op.token :: (right.tokens ++ .symbol ';' :: rest))
        (fun name mem => names name (by simp [InfixLeaf.identifiers, mem]))
        (by simp only [InfixLeaf.size] at enough; omega) (by simp [BinaryOp.token_ne_open])
      have tailParse := parseInfixTail_infix op right fuel
        (fun name mem => names name (by simp [InfixLeaf.identifiers, mem]))
        (by simp only [InfixLeaf.size] at enough; omega) rest
      simp only [InfixLeaf.tokens, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseInfixLeaf, notLet, notReserved, expectTokens, leftParse, tailParse]

theorem InfixLeaf.blockEnds_tokens (statement : InfixLeaf) (names : statement.NamesOk)
    (rest : List Token) : blockEnds (statement.tokens ++ rest) = false := by
  cases statement with
  | plain statement => exact Stmt.blockEnds_tokens statement names rest
  | letInfix => rfl
  | assignInfix identifier op left right =>
      have notReserved := names identifier (by simp [InfixLeaf.identifiers])
      have notReturn := (not_reserved_ne notReserved).2.2.1
      simp [InfixLeaf.tokens, blockEnds, notReturn]

theorem parseInfixLeaves_tokens : ∀ (statements : List InfixLeaf) (fuel : Nat)
    (rest : List Token), InfixLeaf.ListNamesOk statements →
    InfixLeaf.listSize statements < fuel → blockEnds rest = true →
    parseInfixLeaves fuel (InfixLeaf.listTokens statements ++ rest) = some (statements, rest)
  | [], fuel + 1, rest, _, _, ends => by simp [InfixLeaf.listTokens, parseInfixLeaves, ends]
  | statement :: tail, fuel + 1, rest, names, enough, ends => by
      have statementNames : statement.NamesOk := fun name mem =>
        names name (by simp [InfixLeaf.listIdentifiers, mem])
      have statementParse := parseInfixLeaf_tokens statement statementNames fuel
        (by simp only [InfixLeaf.listSize] at enough; omega) (InfixLeaf.listTokens tail ++ rest)
      have tailParse := parseInfixLeaves_tokens tail fuel rest
        (fun name mem => names name (by simp [InfixLeaf.listIdentifiers, mem]))
        (by simp only [InfixLeaf.listSize] at enough; omega) ends
      simp only [InfixLeaf.listTokens, List.append_assoc]
      simp [parseInfixLeaves, InfixLeaf.blockEnds_tokens statement statementNames,
        statementParse, tailParse]
  | _, 0, _, _, enough, _ => absurd enough (Nat.not_lt_zero _)

/-- A leaf that is not a `match` does not start with `match`. -/
theorem InfixLeaf.tokens_ne_match (statement : InfixLeaf) (names : statement.NamesOk)
    (canonical : (InfixStmt.leaf statement).Canonical) (rest more : List Token) :
    statement.tokens ++ rest ≠ .ident "match" :: more := by
  intro same
  cases statement with
  | plain statement =>
      cases statement with
      | letDecl => simp [InfixLeaf.tokens, Stmt.tokens] at same
      | assign identifier value =>
          have notMatch := (not_reserved_ne
            (names identifier (by simp [InfixLeaf.identifiers, Stmt.identifiers]))).2.2.2
          simp [InfixLeaf.tokens, Stmt.tokens] at same
          exact notMatch same.1
      | ifElse => simp [InfixLeaf.tokens, Stmt.tokens] at same
      | matchPair => cases canonical
      | matchSum => cases canonical
  | letInfix => simp [InfixLeaf.tokens] at same
  | assignInfix identifier op left right =>
      have notMatch := (not_reserved_ne
        (names identifier (by simp [InfixLeaf.identifiers]))).2.2.2
      simp [InfixLeaf.tokens] at same
      exact notMatch same.1

theorem InfixStmt.blockEnds_tokens (statement : InfixStmt)
    (names : ∀ name ∈ statement.identifiers, isReserved name = false) (rest : List Token) :
    blockEnds (statement.tokens ++ rest) = false := by
  cases statement with
  | leaf statement => exact InfixLeaf.blockEnds_tokens statement names rest
  | matchPair => simp [InfixStmt.tokens, blockEnds]
  | matchSum => simp [InfixStmt.tokens, blockEnds]

theorem parseInfixStmt_tokens (statement : InfixStmt)
    (names : ∀ name ∈ statement.identifiers, isReserved name = false)
    (canonical : statement.Canonical) (fuel : Nat) (enough : statement.size < fuel)
    (rest : List Token) :
    parseInfixStmt fuel (statement.tokens ++ rest) = some (statement, rest) := by
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
  cases statement with
  | leaf statement =>
      have notMatch : (statement.tokens ++ rest).head? ≠ some (.ident "match") := by
        intro same
        cases shape : statement.tokens ++ rest with
        | nil => simp [shape] at same
        | cons first more =>
            rw [shape] at same
            simp only [List.head?_cons, Option.some.injEq] at same
            subst same
            exact InfixLeaf.tokens_ne_match statement names canonical rest more shape
      have leafParse := parseInfixLeaf_tokens statement names (fuel + 1)
        (by simpa [InfixStmt.size] using enough) rest
      show parseInfixStmt (fuel + 1) (statement.tokens ++ rest) = _
      rw [parseInfixStmt, if_neg notMatch, leafParse]
      rfl
  | matchPair scrutinee first second body =>
      have firstOk : isReserved first = false := names first (by simp [InfixStmt.identifiers])
      have secondOk : isReserved second = false := names second (by simp [InfixStmt.identifiers])
      have bodyParse := parseInfixLeaves_tokens body fuel ([.symbol '}', .symbol '}'] ++ rest)
        (fun name mem => names name (by simp [InfixStmt.identifiers, mem]))
        (by simp only [InfixStmt.size] at enough; omega) rfl
      have scrutineeParse := parseExpr_tokens scrutinee fuel
        ([.symbol ')', .symbol '{', .ident "case", .symbol '(', .ident first, .symbol ',',
          .ident second, .symbol ')', .symbol '{'] ++ InfixLeaf.listTokens body ++
          [.symbol '}', .symbol '}'] ++ rest)
        (fun name mem => names name (by simp [InfixStmt.identifiers, mem]))
        (by simp only [InfixStmt.size] at enough; omega) (by simp)
      simp only [List.cons_append, List.nil_append] at bodyParse
      simp only [List.append_assoc, List.cons_append, List.nil_append] at scrutineeParse
      simp only [InfixStmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseInfixStmt, expectTokens, scrutineeParse, parseName_cons firstOk,
        parseName_cons secondOk, bodyParse]
  | matchSum scrutinee left leftBody right rightBody =>
      have leftOk : isReserved left = false := names left (by simp [InfixStmt.identifiers])
      have rightOk : isReserved right = false := names right (by simp [InfixStmt.identifiers])
      have rightParse := parseInfixLeaves_tokens rightBody fuel
        ([.symbol '}', .symbol '}'] ++ rest)
        (fun name mem => names name (by simp [InfixStmt.identifiers, mem]))
        (by simp only [InfixStmt.size] at enough; omega) rfl
      have leftParse := parseInfixLeaves_tokens leftBody fuel
        ([.symbol '}', .ident "case", .ident "inr", .symbol '(', .ident right, .symbol ')',
          .symbol '{'] ++ InfixLeaf.listTokens rightBody ++ [.symbol '}', .symbol '}'] ++ rest)
        (fun name mem => names name (by simp [InfixStmt.identifiers, mem]))
        (by simp only [InfixStmt.size] at enough; omega) rfl
      have scrutineeParse := parseExpr_tokens scrutinee fuel
        ([.symbol ')', .symbol '{', .ident "case", .ident "inl", .symbol '(', .ident left,
          .symbol ')', .symbol '{'] ++ InfixLeaf.listTokens leftBody ++
          [.symbol '}', .ident "case", .ident "inr", .symbol '(', .ident right, .symbol ')',
            .symbol '{'] ++ InfixLeaf.listTokens rightBody ++ [.symbol '}', .symbol '}'] ++ rest)
        (fun name mem => names name (by simp [InfixStmt.identifiers, mem]))
        (by simp only [InfixStmt.size] at enough; omega) (by simp)
      simp only [List.cons_append, List.nil_append] at rightParse
      simp only [List.append_assoc, List.cons_append, List.nil_append] at leftParse
      simp only [List.append_assoc, List.cons_append, List.nil_append] at scrutineeParse
      simp only [InfixStmt.tokens, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseInfixStmt, expectTokens, scrutineeParse, parseName_cons leftOk,
        parseName_cons rightOk, leftParse, rightParse]

theorem parseInfixStmts_tokens : ∀ (statements : List InfixStmt) (fuel : Nat)
    (rest : List Token), InfixStmt.ListNamesOk statements →
    (∀ statement ∈ statements, statement.Canonical) →
    InfixStmt.listSize statements < fuel → blockEnds rest = true →
    parseInfixStmts fuel (InfixStmt.listTokens statements ++ rest) = some (statements, rest)
  | [], fuel + 1, rest, _, _, _, ends => by simp [InfixStmt.listTokens, parseInfixStmts, ends]
  | statement :: tail, fuel + 1, rest, names, canonical, enough, ends => by
      have statementNames : ∀ name ∈ statement.identifiers, isReserved name = false :=
        fun name mem => names name (by simp [InfixStmt.listIdentifiers, mem])
      have statementCanonical := canonical statement (by simp)
      have statementParse := parseInfixStmt_tokens statement statementNames statementCanonical
        fuel (by simp only [InfixStmt.listSize] at enough; omega)
        (InfixStmt.listTokens tail ++ rest)
      have tailParse := parseInfixStmts_tokens tail fuel rest
        (fun name mem => names name (by simp [InfixStmt.listIdentifiers, mem]))
        (fun other mem => canonical other (List.mem_cons_of_mem _ mem))
        (by simp only [InfixStmt.listSize] at enough; omega) ends
      simp only [InfixStmt.listTokens, List.append_assoc]
      simp [parseInfixStmts, InfixStmt.blockEnds_tokens statement statementNames,
        statementParse, tailParse]
  | _, 0, _, _, _, enough, _ => absurd enough (Nat.not_lt_zero _)

/-! ### Parser round trip: files -/

theorem Stmt.size_lt_tokens (statement : Stmt) : statement.size < statement.tokens.length :=
  (Stmt.size_bounds (statement.size + 1)).1 statement (Nat.lt_succ_self _)

theorem GuardStmt.listSize_le_tokens : (statements : List GuardStmt) →
    GuardStmt.listSize statements ≤ (GuardStmt.listTokens statements).length
  | [] => by simp [GuardStmt.listSize, GuardStmt.listTokens]
  | .plain statement :: rest => by
      have := Stmt.size_lt_tokens statement
      have := GuardStmt.listSize_le_tokens rest
      simp [GuardStmt.listSize, GuardStmt.size, GuardStmt.listTokens, GuardStmt.tokens]
      omega
  | .guard condition value :: rest => by
      have := Expr.size_le_tokens value
      have := GuardStmt.listSize_le_tokens rest
      simp [GuardStmt.listSize, GuardStmt.size, GuardStmt.listTokens, GuardStmt.tokens,
        guardTokens]
      omega

theorem InfixLeaf.listSize_le_tokens : (statements : List InfixLeaf) →
    InfixLeaf.listSize statements ≤ (InfixLeaf.listTokens statements).length
  | [] => by simp [InfixLeaf.listSize, InfixLeaf.listTokens]
  | .plain statement :: rest => by
      have := Stmt.size_lt_tokens statement
      have := InfixLeaf.listSize_le_tokens rest
      simp [InfixLeaf.listSize, InfixLeaf.size, InfixLeaf.listTokens, InfixLeaf.tokens]
      omega
  | .letInfix _ type _ left right :: rest => by
      have := Expr.size_le_tokens left
      have := Expr.size_le_tokens right
      have := InfixLeaf.listSize_le_tokens rest
      simp [InfixLeaf.listSize, InfixLeaf.size, InfixLeaf.listTokens, InfixLeaf.tokens]
      omega
  | .assignInfix _ _ left right :: rest => by
      have := Expr.size_le_tokens left
      have := Expr.size_le_tokens right
      have := InfixLeaf.listSize_le_tokens rest
      simp [InfixLeaf.listSize, InfixLeaf.size, InfixLeaf.listTokens, InfixLeaf.tokens]
      omega

theorem InfixStmt.listSize_le_tokens : (statements : List InfixStmt) →
    InfixStmt.listSize statements ≤ (InfixStmt.listTokens statements).length
  | [] => by simp [InfixStmt.listSize, InfixStmt.listTokens]
  | .leaf statement :: rest => by
      have := InfixLeaf.listSize_le_tokens [statement]
      have := InfixStmt.listSize_le_tokens rest
      simp [InfixLeaf.listSize, InfixLeaf.listTokens] at *
      simp [InfixStmt.listSize, InfixStmt.size, InfixStmt.listTokens, InfixStmt.tokens]
      omega
  | .matchPair scrutinee _ _ body :: rest => by
      have := Expr.size_le_tokens scrutinee
      have := InfixLeaf.listSize_le_tokens body
      have := InfixStmt.listSize_le_tokens rest
      simp [InfixStmt.listSize, InfixStmt.size, InfixStmt.listTokens, InfixStmt.tokens]
      omega
  | .matchSum scrutinee _ leftBody _ rightBody :: rest => by
      have := Expr.size_le_tokens scrutinee
      have := InfixLeaf.listSize_le_tokens leftBody
      have := InfixLeaf.listSize_le_tokens rightBody
      have := InfixStmt.listSize_le_tokens rest
      simp [InfixStmt.listSize, InfixStmt.size, InfixStmt.listTokens, InfixStmt.tokens]
      omega

theorem GenericDecl.sizes_le_tokens (declaration : GenericDecl) :
    GuardStmt.listSize declaration.body < declaration.tokens.length ∧
      declaration.result.size < declaration.tokens.length := by
  have bodySize := GuardStmt.listSize_le_tokens declaration.body
  have resultSize := Expr.size_le_tokens declaration.result
  simp only [GenericDecl.tokens, List.length_append, List.length_cons, List.length_nil]
  omega

theorem generics_sizes_le_tokens {generics : List GenericDecl} {declaration : GenericDecl}
    (mem : declaration ∈ generics) :
    GuardStmt.listSize declaration.body < (generics.flatMap GenericDecl.tokens).length ∧
      declaration.result.size < (generics.flatMap GenericDecl.tokens).length := by
  induction generics with
  | nil => cases mem
  | cons head rest ih =>
      simp only [List.flatMap_cons, List.length_append]
      rcases List.mem_cons.mp mem with same | mem
      · subst same
        have := declaration.sizes_le_tokens
        omega
      · have := ih mem
        omega

theorem generics_length_le_tokens (generics : List GenericDecl) :
    generics.length ≤ (generics.flatMap GenericDecl.tokens).length := by
  induction generics with
  | nil => simp
  | cons declaration rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have : 1 ≤ declaration.tokens.length := by simp [GenericDecl.tokens]
      omega

theorem parseGenericFileWith_tokens (file : GenericFile) (names : file.NamesOk) (fuel : Nat)
    (genericsFuel : ∀ declaration ∈ file.generics,
      GuardStmt.listSize declaration.body < fuel ∧ declaration.result.size < fuel)
    (functionsFuel : ∀ function ∈ file.functions,
      Stmt.listSize function.body < fuel ∧ function.result.size < fuel)
    (bodyFuel : InfixStmt.listSize file.method.body < fuel)
    (resultFuel : file.method.result.size < fuel) :
    parseGenericFileWith fuel file.tokens = some file := by
  obtain ⟨genericsOk, functionsOk, contractOk, methodOk, parametersOk, bodyOk, canonical,
    resultOk⟩ := names
  have bodyParse := parseInfixStmts_tokens file.method.body fuel
    (.ident "return" :: (file.method.result.tokens ++
      [.symbol ';', .symbol '}', .symbol '}'])) bodyOk canonical bodyFuel rfl
  have resultParse := parseExpr_tokens file.method.result fuel
    [.symbol ';', .symbol '}', .symbol '}'] resultOk resultFuel (by simp)
  have parametersParse := parseParameters_tokens file.method.parameters
    (signatureTokens ++ (InfixStmt.listTokens file.method.body ++ (.ident "return" ::
      (file.method.result.tokens ++ [.symbol ';', .symbol '}', .symbol '}'])))) parametersOk rfl
  have functionsLength := functions_length_le_tokens file.functions
  have genericsLength := generics_length_le_tokens file.generics
  have functionsParse := parseFunctions_tokens file.functions (file.tokens.length + 1) fuel
    (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
      .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
        (signatureTokens ++ (InfixStmt.listTokens file.method.body ++ (.ident "return" ::
          (file.method.result.tokens ++ [.symbol ';', .symbol '}', .symbol '}']))))))
    (fun function mem => ⟨functionsOk function mem, functionsFuel function mem⟩)
    (by simp only [GenericFile.tokens, List.length_append] at functionsLength ⊢; omega)
    (by simp)
  have notGeneric : startsGeneric (file.functions.flatMap FunctionDecl.tokens ++
      (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
        .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
          (signatureTokens ++ (InfixStmt.listTokens file.method.body ++ (.ident "return" ::
            (file.method.result.tokens ++ [.symbol ';', .symbol '}', .symbol '}']))))))) =
      false := by
    cases functions : file.functions with
    | nil => simp [startsGeneric]
    | cons function rest => simp [startsGeneric, FunctionDecl.tokens]
  have genericsParse := parseGenerics_tokens file.generics (file.tokens.length + 1) fuel
    (file.functions.flatMap FunctionDecl.tokens ++
      (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
        .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
          (signatureTokens ++ (InfixStmt.listTokens file.method.body ++ (.ident "return" ::
            (file.method.result.tokens ++ [.symbol ';', .symbol '}', .symbol '}'])))))))
    (fun declaration mem => ⟨genericsOk declaration mem, genericsFuel declaration mem⟩)
    (by simp only [GenericFile.tokens, List.length_append] at genericsLength ⊢; omega)
    notGeneric
  have aliasesParse := parseAliasImport_tokens file.opcodeAliases
    (file.generics.flatMap GenericDecl.tokens ++ (file.functions.flatMap FunctionDecl.tokens ++
      (.ident "contract" :: .ident file.contract :: .symbol '{' :: .ident "function" ::
        .ident file.method.name :: .symbol '(' :: (parameterTokens file.method.parameters ++
          (signatureTokens ++ (InfixStmt.listTokens file.method.body ++ (.ident "return" ::
            (file.method.result.tokens ++ [.symbol ';', .symbol '}', .symbol '}']))))))))
    (by
      cases generics : file.generics with
      | nil =>
          cases functions : file.functions with
          | nil => simp
          | cons function rest => simp [FunctionDecl.tokens]
      | cons declaration rest => simp [GenericDecl.tokens])
  unfold parseGenericFileWith
  conv => lhs; arg 1; rw [GenericFile.tokens]
  simp only [List.append_assoc, List.cons_append, List.nil_append, expectTokens_append,
    Option.bind_eq_bind, Option.bind_some]
  rw [aliasesParse]
  simp only [Option.bind_some]
  rw [genericsParse]
  simp only [Option.bind_some]
  rw [functionsParse]
  simp [expectTokens, parseName_cons contractOk, parseName_cons methodOk, parametersParse,
    expectTokens_append, bodyParse, resultParse]

/-- **Parser round trip.** Parsing the tokens of a generic file with
non-reserved names returns that file. -/
theorem parseGenericFile_tokens (file : GenericFile) (names : file.NamesOk) :
    parseGenericFile file.tokens = some file := by
  have bodySize := InfixStmt.listSize_le_tokens file.method.body
  have resultSize := Expr.size_le_tokens file.method.result
  apply parseGenericFileWith_tokens file names
  · intro declaration mem
    have := generics_sizes_le_tokens mem
    simp only [GenericFile.tokens, List.length_append]
    omega
  · intro function mem
    have := functions_sizes_le_tokens mem
    simp only [GenericFile.tokens, List.length_append]
    omega
  · simp only [GenericFile.tokens, List.length_append] at bodySize ⊢
    omega
  · simp only [GenericFile.tokens, List.length_append] at resultSize ⊢
    omega

/-! ### Printed pieces: signatures and generic functions -/

def TypeRef.pieces : TypeRef → List Piece
  | .concrete type => type.pieces
  | .param name => [word name]

theorem TypeRef.spelling_toList (type : TypeRef) : type.spelling.toList = render type.pieces := by
  cases type with
  | concrete type => exact LocalType.spelling_toList type
  | param name => simp [TypeRef.spelling, TypeRef.pieces, render, Piece.chars, Token.chars, word]

theorem TypeRef.tokensOf_pieces (type : TypeRef) : tokensOf type.pieces = type.tokens := by
  cases type with
  | concrete type => exact LocalType.tokensOf_pieces type
  | param name => rfl

theorem TypeRef.separated_append (type : TypeRef)
    (valid : ∀ name ∈ type.identifiers, ValidIdentifier name) (rest : List Piece)
    (separated : Separated rest) (safe : ∀ next ∈ rest.head?, next.SafeLeft) :
    Separated (type.pieces ++ rest) := by
  cases type with
  | concrete type => exact LocalType.separated_append type rest separated safe
  | param name =>
      exact Separated.cons_word (valid name (by simp [TypeRef.identifiers])) separated safe

def typeParameterPieces : List String → List Piece
  | [] => []
  | [name] => [word name]
  | name :: next :: rest => [word name, sym ',', space] ++ typeParameterPieces (next :: rest)

theorem typeParameterText_toList : (names : List String) →
    (typeParameterText names).toList = render (typeParameterPieces names)
  | [] => rfl
  | [name] => by
      simp [typeParameterText, typeParameterPieces, render, Piece.chars, Token.chars, word]
  | name :: next :: rest => by
      have tail := typeParameterText_toList (next :: rest)
      simp only [typeParameterText] at tail ⊢
      rw [String.intercalate_cons_cons, String.toList_append, String.toList_append, tail]
      simp [typeParameterPieces, render, Piece.chars, Token.chars, word, sym, space]

theorem typeParameterPieces_tokens : (names : List String) →
    tokensOf (typeParameterPieces names) = typeParameterTokens names
  | [] => rfl
  | [_] => rfl
  | name :: next :: rest => by
      simp [typeParameterPieces, typeParameterTokens, tokensOf, word, sym, space,
        typeParameterPieces_tokens (next :: rest)]

theorem typeParameterPieces_separated : (names : List String) →
    (∀ name ∈ names, ValidIdentifier name) →
    ∀ rest, Separated rest → (∀ next ∈ rest.head?, next.SafeLeft) →
    Separated (typeParameterPieces names ++ rest)
  | [], _, _, separated, _ => separated
  | [name], valid, rest, separated, safe => by
      simp only [typeParameterPieces, List.cons_append, List.nil_append]
      exact Separated.cons_word (valid name (by simp)) separated safe
  | name :: next :: more, valid, rest, separated, safe => by
      have tail := typeParameterPieces_separated (next :: more)
        (fun other mem => valid other (List.mem_cons_of_mem _ mem)) rest separated safe
      simp only [typeParameterPieces, List.cons_append, List.nil_append]
      exact Separated.cons_word (valid name (by simp)) (Separated.cons_sym (by decide)
        (Separated.cons_space tail)) (head_sym (by decide))

def genericParameterPieces : List (String × TypeRef) → List Piece
  | [] => []
  | [parameter] => [word parameter.1, sym ':', space] ++ parameter.2.pieces
  | parameter :: next :: rest =>
      [word parameter.1, sym ':', space] ++ parameter.2.pieces ++ [sym ',', space] ++
        genericParameterPieces (next :: rest)

theorem genericParameterText_toList : (parameters : List (String × TypeRef)) →
    (genericParameterText parameters).toList = render (genericParameterPieces parameters)
  | [] => rfl
  | [parameter] => by
      simp [genericParameterText, genericParameterPieces, render, Piece.chars, Token.chars, word,
        sym, space, TypeRef.spelling_toList]
  | parameter :: next :: rest => by
      have tail := genericParameterText_toList (next :: rest)
      simp only [genericParameterText, List.map_cons] at tail ⊢
      rw [String.intercalate_cons_cons, String.toList_append, String.toList_append, tail]
      simp [genericParameterPieces, render, render_append, Piece.chars, Token.chars, word, sym,
        space, TypeRef.spelling_toList]

theorem genericParameterPieces_tokens : (parameters : List (String × TypeRef)) →
    tokensOf (genericParameterPieces parameters) = genericParameterTokens parameters
  | [] => rfl
  | [_] => by
      simp [genericParameterPieces, genericParameterTokens, tokensOf, word, sym, space,
        TypeRef.tokensOf_pieces]
  | parameter :: next :: rest => by
      simp [genericParameterPieces, genericParameterTokens, tokensOf, tokensOf_append, word,
        sym, space, TypeRef.tokensOf_pieces, genericParameterPieces_tokens (next :: rest)]

theorem genericParameterPieces_separated : (parameters : List (String × TypeRef)) →
    (∀ parameter ∈ parameters, ValidIdentifier parameter.1 ∧
      ∀ name ∈ parameter.2.identifiers, ValidIdentifier name) →
    ∀ rest, Separated rest → (∀ next ∈ rest.head?, next.SafeLeft) →
    Separated (genericParameterPieces parameters ++ rest)
  | [], _, _, separated, _ => separated
  | [parameter], valid, rest, separated, safe => by
      obtain ⟨nameValid, typeValid⟩ := valid parameter (by simp)
      simp only [genericParameterPieces, List.cons_append, List.nil_append]
      exact Separated.cons_word nameValid (Separated.cons_sym (by decide)
        (Separated.cons_space (TypeRef.separated_append _ typeValid _ separated safe)))
        (head_sym (by decide))
  | parameter :: next :: more, valid, rest, separated, safe => by
      obtain ⟨nameValid, typeValid⟩ := valid parameter (by simp)
      have tail := genericParameterPieces_separated (next :: more)
        (fun other mem => valid other (List.mem_cons_of_mem _ mem)) rest separated safe
      simp only [genericParameterPieces, List.cons_append, List.nil_append, List.append_assoc]
      exact Separated.cons_word nameValid (Separated.cons_sym (by decide)
        (Separated.cons_space (TypeRef.separated_append _ typeValid _
          (Separated.cons_sym (by decide) (Separated.cons_space tail))
          (head_sym (by decide))))) (head_sym (by decide))

def GuardStmt.linePieces (indent : Nat) : GuardStmt → List (List Piece)
  | .plain statement => statement.linePieces indent
  | .guard condition value =>
      [blanks indent ++ [word "if", space, sym '(', word condition, sym ')', space, sym '{'],
        blanks (indent + 4) ++ [word "return", space] ++ value.pieces ++ [sym ';'],
        blanks indent ++ [sym '}']]

def GuardStmt.listLinePieces (indent : Nat) : List GuardStmt → List (List Piece)
  | [] => []
  | statement :: rest => statement.linePieces indent ++ GuardStmt.listLinePieces indent rest

theorem GuardStmt.lines_toList (indent : Nat) : (statement : GuardStmt) →
    (statement.lines indent).map String.toList = (statement.linePieces indent).map render
  | .plain statement => Stmt.lines_toList indent statement
  | .guard condition value => by
      simp [GuardStmt.lines, GuardStmt.linePieces, indentLine_toList, render_append,
        render_blanks, render, Piece.chars, Token.chars, word, sym, space, Expr.print_toList]

theorem GuardStmt.listLines_toList (indent : Nat) : (statements : List GuardStmt) →
    (GuardStmt.listLines indent statements).map String.toList =
      (GuardStmt.listLinePieces indent statements).map render
  | [] => rfl
  | statement :: rest => by
      simp [GuardStmt.listLines, GuardStmt.listLinePieces, GuardStmt.lines_toList indent statement,
        GuardStmt.listLines_toList indent rest]

theorem GuardStmt.linePieces_tokens (indent : Nat) : (statement : GuardStmt) →
    ((statement.linePieces indent).map tokensOf).flatten = statement.tokens
  | .plain statement => Stmt.linePieces_tokens indent statement
  | .guard condition value => by
      simp [GuardStmt.linePieces, GuardStmt.tokens, guardTokens, tokensOf_append,
        tokensOf_blanks, tokensOf, word, sym, space, Expr.tokensOf_pieces]

theorem GuardStmt.listLinePieces_tokens (indent : Nat) : (statements : List GuardStmt) →
    ((GuardStmt.listLinePieces indent statements).map tokensOf).flatten =
      GuardStmt.listTokens statements
  | [] => rfl
  | statement :: rest => by
      simp [GuardStmt.listLinePieces, GuardStmt.listTokens,
        GuardStmt.linePieces_tokens indent statement, GuardStmt.listLinePieces_tokens indent rest]

theorem GuardStmt.linePieces_separated (indent : Nat) : (statement : GuardStmt) →
    (∀ name ∈ statement.identifiers, ValidIdentifier name) →
    ∀ line ∈ statement.linePieces indent, Separated line
  | .plain statement, valid, line, mem =>
      Stmt.linePieces_separated indent statement valid line mem
  | .guard condition value, valid, line, mem => by
      simp only [GuardStmt.linePieces, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with same | same | same
      · subst same
        exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_space (Separated.cons_sym (by decide) (Separated.cons_word
            (valid condition (by simp [GuardStmt.identifiers])) (Separated.cons_sym (by decide)
              (Separated.cons_space (sym_valid (by decide)))) (head_sym (by decide)))))
          head_space)
      · subst same
        have valuePart := Expr.separated_append value
          (fun name mem => valid name (by simp [GuardStmt.identifiers, mem])) [sym ';']
          (sym_valid (by decide)) (head_sym (by decide))
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        exact Separated.blanks_append (indent + 4) (Separated.cons_word
          (keyword_valid (by decide)) (Separated.cons_space valuePart) head_space)
      · subst same
        exact Separated.blanks_append indent (sym_valid (by decide))

theorem GuardStmt.listLinePieces_separated (indent : Nat) : (statements : List GuardStmt) →
    (∀ name ∈ GuardStmt.listIdentifiers statements, ValidIdentifier name) →
    ∀ line ∈ GuardStmt.listLinePieces indent statements, Separated line
  | [], _, _, mem => by simp [GuardStmt.listLinePieces] at mem
  | statement :: rest, valid, line, mem => by
      simp only [GuardStmt.listLinePieces, List.mem_append] at mem
      rcases mem with mem | mem
      · exact GuardStmt.linePieces_separated indent statement
          (fun name found => valid name (by simp [GuardStmt.listIdentifiers, found])) line mem
      · exact GuardStmt.listLinePieces_separated indent rest
          (fun name found => valid name (by simp [GuardStmt.listIdentifiers, found])) line mem

/-- One piece list per printed line of a generic function. -/
def GenericDecl.linePieces (declaration : GenericDecl) : List (List Piece) :=
  [[word "function", space, word declaration.name, sym '<'] ++
      typeParameterPieces declaration.typeParameters ++ [sym '>', sym '('] ++
      genericParameterPieces declaration.parameters ++
      [sym ')', space, word "returns", space, sym '('] ++ declaration.resultType.pieces ++
      [sym ')', space, sym '{']] ++
    GuardStmt.listLinePieces 4 declaration.body ++
    [blanks 4 ++ [word "return", space] ++ declaration.result.pieces ++ [sym ';'], [sym '}'],
      []]

theorem GenericDecl.lines_toList (declaration : GenericDecl) :
    declaration.lines.map String.toList = declaration.linePieces.map render := by
  simp [GenericDecl.lines, GenericDecl.linePieces, GuardStmt.listLines_toList,
    typeParameterText_toList, genericParameterText_toList, Expr.print_toList, render_append,
    render_blanks, render, Piece.chars, Token.chars, word, sym, space, TypeRef.spelling_toList]

theorem GenericDecl.linePieces_tokens (declaration : GenericDecl) :
    (declaration.linePieces.map tokensOf).flatten = declaration.tokens := by
  simp [GenericDecl.linePieces, GenericDecl.tokens, GuardStmt.listLinePieces_tokens,
    typeParameterPieces_tokens, genericParameterPieces_tokens, Expr.tokensOf_pieces,
    tokensOf_append, tokensOf_blanks, tokensOf, word, sym, space, TypeRef.tokensOf_pieces]

theorem GenericDecl.linePieces_separated (declaration : GenericDecl)
    (valid : ∀ name ∈ declaration.identifiers, ValidIdentifier name) :
    ∀ line ∈ declaration.linePieces, Separated line := by
  have nameValid : ValidIdentifier declaration.name :=
    valid declaration.name (by simp [GenericDecl.identifiers])
  have typeParametersValid : ∀ name ∈ declaration.typeParameters, ValidIdentifier name :=
    fun name mem => valid name (by simp [GenericDecl.identifiers, mem])
  have parametersValid : ∀ parameter ∈ declaration.parameters, ValidIdentifier parameter.1 ∧
      ∀ name ∈ parameter.2.identifiers, ValidIdentifier name := by
    have inner : ∀ (parameters : List (String × TypeRef)),
        (∀ name ∈ genericParameterIdentifiers parameters, ValidIdentifier name) →
        ∀ parameter ∈ parameters, ValidIdentifier parameter.1 ∧
          ∀ name ∈ parameter.2.identifiers, ValidIdentifier name := by
      intro parameters
      induction parameters with
      | nil => intro _ _ absent; cases absent
      | cons first more ih =>
          intro all parameter mem
          rcases List.mem_cons.mp mem with same | mem
          · subst same
            exact ⟨all _ (by simp [genericParameterIdentifiers]),
              fun name found => all name (by simp [genericParameterIdentifiers, found])⟩
          · exact ih (fun name found => all name (by
              simp [genericParameterIdentifiers, found])) parameter mem
    exact inner declaration.parameters
      (fun name mem => valid name (by simp [GenericDecl.identifiers, mem]))
  have resultTypeValid : ∀ name ∈ declaration.resultType.identifiers, ValidIdentifier name :=
    fun name mem => valid name (by simp [GenericDecl.identifiers, mem])
  have bodyValid : ∀ name ∈ GuardStmt.listIdentifiers declaration.body, ValidIdentifier name :=
    fun name mem => valid name (by simp [GenericDecl.identifiers, mem])
  have resultValid : declaration.result.IdentifiersValid :=
    fun name mem => valid name (by simp [GenericDecl.identifiers, mem])
  intro line mem
  simp only [GenericDecl.linePieces, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at mem
  rcases mem with (same | mem) | same | same | same
  · subst same
    have resultTypePart := TypeRef.separated_append declaration.resultType resultTypeValid
      [sym ')', space, sym '{'] (Separated.cons_sym (by decide) (Separated.cons_space
        (sym_valid (by decide)))) (head_sym (by decide))
    have parametersPart := genericParameterPieces_separated declaration.parameters
      parametersValid ([sym ')', space, word "returns", space, sym '('] ++
        declaration.resultType.pieces ++ [sym ')', space, sym '{'])
      (Separated.cons_sym (by decide) (Separated.cons_space (Separated.cons_word
        (keyword_valid (by decide)) (Separated.cons_space (Separated.cons_sym (by decide)
          (by simpa using resultTypePart))) head_space)))
      (head_sym (by decide))
    have typeParametersPart := typeParameterPieces_separated declaration.typeParameters
      typeParametersValid ([sym '>', sym '('] ++ genericParameterPieces declaration.parameters ++
        [sym ')', space, word "returns", space, sym '('] ++ declaration.resultType.pieces ++
        [sym ')', space, sym '{'])
      (Separated.cons_sym (by decide) (Separated.cons_sym (by decide)
        (by simpa using parametersPart)))
      (head_sym (by decide))
    simp only [List.cons_append, List.nil_append, List.append_assoc] at typeParametersPart ⊢
    exact Separated.cons_word (keyword_valid (by decide)) (Separated.cons_space
      (Separated.cons_word nameValid (Separated.cons_sym (by decide) typeParametersPart)
        (head_sym (by decide)))) head_space
  · exact GuardStmt.listLinePieces_separated 4 declaration.body bodyValid line mem
  · subst same
    have resultPart := Expr.separated_append declaration.result resultValid [sym ';']
      (sym_valid (by decide)) (head_sym (by decide))
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact Separated.blanks_append 4 (Separated.cons_word (keyword_valid (by decide))
      (Separated.cons_space resultPart) head_space)
  · subst same
    exact sym_valid (by decide)
  · subst same
    trivial

/-! ### Printed pieces: infix statements and files -/

/-- One infix operation without parentheses, followed by `;`. -/
def infixPieces (op : BinaryOp) (left right : Expr) : List Piece :=
  left.pieces ++ [space, .token op.token, space] ++ right.pieces ++ [sym ';']

theorem infixPieces_render (op : BinaryOp) (left right : Expr) :
    (infixText op left right).toList ++ [';'] = render (infixPieces op left right) := by
  simp [infixText, infixPieces, render_append, render, Piece.chars, Token.chars, sym, space,
    Expr.print_toList, BinaryOp.spelling_toList]

theorem infixPieces_tokens (op : BinaryOp) (left right : Expr) :
    tokensOf (infixPieces op left right) = left.tokens ++ [op.token] ++ right.tokens ++
      [.symbol ';'] := by
  simp [infixPieces, tokensOf_append, tokensOf, sym, space, Expr.tokensOf_pieces]

/-- An infix operation and `;` are separated. -/
theorem infixPieces_separated (op : BinaryOp) (left right : Expr)
    (leftValid : left.IdentifiersValid) (rightValid : right.IdentifiersValid) :
    Separated (infixPieces op left right) := by
  have rightPart := Expr.separated_append right rightValid [sym ';'] (sym_valid (by decide))
    (head_sym (by decide))
  have middle : Separated (space :: .token op.token :: space :: (right.pieces ++ [sym ';'])) :=
    Separated.cons_space (Separated.cons_safe (BinaryOp.token_valid op).1
      (BinaryOp.token_valid op).2 (Separated.cons_space rightPart))
  have leftPart := Expr.separated_append left leftValid _ middle
    (fun next same => by cases same; exact space_safeLeft)
  simpa [infixPieces, List.append_assoc] using leftPart

def InfixLeaf.linePieces (indent : Nat) : InfixLeaf → List (List Piece)
  | .plain statement => statement.linePieces indent
  | .letInfix identifier type op left right =>
      [blanks indent ++ [word "let", space, word identifier, sym ':', space] ++ type.pieces ++
        [space, sym '=', space] ++ infixPieces op left right]
  | .assignInfix identifier op left right =>
      [blanks indent ++ [word identifier, space, sym '=', space] ++ infixPieces op left right]

def InfixLeaf.listLinePieces (indent : Nat) : List InfixLeaf → List (List Piece)
  | [] => []
  | statement :: rest => statement.linePieces indent ++ InfixLeaf.listLinePieces indent rest

theorem InfixLeaf.lines_toList (indent : Nat) : (statement : InfixLeaf) →
    (statement.lines indent).map String.toList = (statement.linePieces indent).map render
  | .plain statement => Stmt.lines_toList indent statement
  | .letInfix identifier type op left right => by
      simp [InfixLeaf.lines, InfixLeaf.linePieces, indentLine_toList, render_append,
        render_blanks, render, Piece.chars, Token.chars, word, sym, space,
        LocalType.spelling_toList, infixPieces_render]
  | .assignInfix identifier op left right => by
      simp [InfixLeaf.lines, InfixLeaf.linePieces, indentLine_toList, render_append,
        render_blanks, render, Piece.chars, Token.chars, word, sym, space, infixPieces_render]

theorem InfixLeaf.listLines_toList (indent : Nat) : (statements : List InfixLeaf) →
    (InfixLeaf.listLines indent statements).map String.toList =
      (InfixLeaf.listLinePieces indent statements).map render
  | [] => rfl
  | statement :: rest => by
      simp [InfixLeaf.listLines, InfixLeaf.listLinePieces, InfixLeaf.lines_toList indent statement,
        InfixLeaf.listLines_toList indent rest]

theorem InfixLeaf.linePieces_tokens (indent : Nat) : (statement : InfixLeaf) →
    ((statement.linePieces indent).map tokensOf).flatten = statement.tokens
  | .plain statement => Stmt.linePieces_tokens indent statement
  | .letInfix identifier type op left right => by
      simp [InfixLeaf.linePieces, InfixLeaf.tokens, tokensOf_append, tokensOf_blanks, tokensOf,
        word, sym, space, LocalType.tokensOf_pieces, infixPieces_tokens]
  | .assignInfix identifier op left right => by
      simp [InfixLeaf.linePieces, InfixLeaf.tokens, tokensOf_append, tokensOf_blanks, tokensOf,
        word, sym, space, infixPieces_tokens]

theorem InfixLeaf.listLinePieces_tokens (indent : Nat) : (statements : List InfixLeaf) →
    ((InfixLeaf.listLinePieces indent statements).map tokensOf).flatten =
      InfixLeaf.listTokens statements
  | [] => rfl
  | statement :: rest => by
      simp [InfixLeaf.listLinePieces, InfixLeaf.listTokens,
        InfixLeaf.linePieces_tokens indent statement, InfixLeaf.listLinePieces_tokens indent rest]

theorem InfixLeaf.linePieces_separated (indent : Nat) : (statement : InfixLeaf) →
    (∀ name ∈ statement.identifiers, ValidIdentifier name) →
    ∀ line ∈ statement.linePieces indent, Separated line
  | .plain statement, valid, line, mem =>
      Stmt.linePieces_separated indent statement valid line mem
  | .letInfix identifier type op left right, valid, line, mem => by
      simp only [InfixLeaf.linePieces, List.mem_singleton] at mem
      subst mem
      have operation := infixPieces_separated op left right
        (fun name mem => valid name (by simp [InfixLeaf.identifiers, mem]))
        (fun name mem => valid name (by simp [InfixLeaf.identifiers, mem]))
      have typePart := LocalType.separated_append type _ (Separated.cons_space
        (Separated.cons_equal (Separated.cons_space operation) (fun next same => by
          cases same; rfl))) head_space
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
        (Separated.cons_space (Separated.cons_word
          (valid identifier (by simp [InfixLeaf.identifiers]))
          (Separated.cons_sym (by decide) (Separated.cons_space typePart))
          (head_sym (by decide))))
        head_space)
  | .assignInfix identifier op left right, valid, line, mem => by
      simp only [InfixLeaf.linePieces, List.mem_singleton] at mem
      subst mem
      have operation := infixPieces_separated op left right
        (fun name mem => valid name (by simp [InfixLeaf.identifiers, mem]))
        (fun name mem => valid name (by simp [InfixLeaf.identifiers, mem]))
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact Separated.blanks_append indent (Separated.cons_word
        (valid identifier (by simp [InfixLeaf.identifiers]))
        (Separated.cons_space (Separated.cons_equal (Separated.cons_space operation)
          (fun next same => by cases same; rfl))) head_space)

theorem InfixLeaf.listLinePieces_separated (indent : Nat) : (statements : List InfixLeaf) →
    (∀ name ∈ InfixLeaf.listIdentifiers statements, ValidIdentifier name) →
    ∀ line ∈ InfixLeaf.listLinePieces indent statements, Separated line
  | [], _, _, mem => by simp [InfixLeaf.listLinePieces] at mem
  | statement :: rest, valid, line, mem => by
      simp only [InfixLeaf.listLinePieces, List.mem_append] at mem
      rcases mem with mem | mem
      · exact InfixLeaf.linePieces_separated indent statement
          (fun name found => valid name (by simp [InfixLeaf.listIdentifiers, found])) line mem
      · exact InfixLeaf.listLinePieces_separated indent rest
          (fun name found => valid name (by simp [InfixLeaf.listIdentifiers, found])) line mem

def InfixStmt.linePieces (indent : Nat) : InfixStmt → List (List Piece)
  | .leaf statement => statement.linePieces indent
  | .matchPair scrutinee first second body =>
      [blanks indent ++ [word "match", space, sym '('] ++ scrutinee.pieces ++
          [sym ')', space, sym '{'],
        blanks (indent + 4) ++ [word "case", space, sym '(', word first, sym ',', space,
          word second, sym ')', space, sym '{']] ++
        InfixLeaf.listLinePieces (indent + 8) body ++
        [blanks (indent + 4) ++ [sym '}'], blanks indent ++ [sym '}']]
  | .matchSum scrutinee left leftBody right rightBody =>
      [blanks indent ++ [word "match", space, sym '('] ++ scrutinee.pieces ++
          [sym ')', space, sym '{'],
        blanks (indent + 4) ++ [word "case", space, word "inl", sym '(', word left, sym ')',
          space, sym '{']] ++
        InfixLeaf.listLinePieces (indent + 8) leftBody ++
        [blanks (indent + 4) ++ [sym '}'],
          blanks (indent + 4) ++ [word "case", space, word "inr", sym '(', word right, sym ')',
            space, sym '{']] ++
        InfixLeaf.listLinePieces (indent + 8) rightBody ++
        [blanks (indent + 4) ++ [sym '}'], blanks indent ++ [sym '}']]

def InfixStmt.listLinePieces (indent : Nat) : List InfixStmt → List (List Piece)
  | [] => []
  | statement :: rest => statement.linePieces indent ++ InfixStmt.listLinePieces indent rest

theorem InfixStmt.lines_toList (indent : Nat) : (statement : InfixStmt) →
    (statement.lines indent).map String.toList = (statement.linePieces indent).map render
  | .leaf statement => InfixLeaf.lines_toList indent statement
  | .matchPair scrutinee first second body => by
      simp [InfixStmt.lines, InfixStmt.linePieces, indentLine_toList, render_append,
        render_blanks, render, Piece.chars, Token.chars, word, sym, space, Expr.print_toList,
        InfixLeaf.listLines_toList (indent + 8) body]
  | .matchSum scrutinee left leftBody right rightBody => by
      simp [InfixStmt.lines, InfixStmt.linePieces, indentLine_toList, render_append,
        render_blanks, render, Piece.chars, Token.chars, word, sym, space, Expr.print_toList,
        InfixLeaf.listLines_toList (indent + 8) leftBody,
        InfixLeaf.listLines_toList (indent + 8) rightBody]

theorem InfixStmt.listLines_toList (indent : Nat) : (statements : List InfixStmt) →
    (InfixStmt.listLines indent statements).map String.toList =
      (InfixStmt.listLinePieces indent statements).map render
  | [] => rfl
  | statement :: rest => by
      simp [InfixStmt.listLines, InfixStmt.listLinePieces, InfixStmt.lines_toList indent statement,
        InfixStmt.listLines_toList indent rest]

theorem InfixStmt.linePieces_tokens (indent : Nat) : (statement : InfixStmt) →
    ((statement.linePieces indent).map tokensOf).flatten = statement.tokens
  | .leaf statement => InfixLeaf.linePieces_tokens indent statement
  | .matchPair scrutinee first second body => by
      simp [InfixStmt.linePieces, InfixStmt.tokens, tokensOf_append, tokensOf_blanks, tokensOf,
        word, sym, space, Expr.tokensOf_pieces, InfixLeaf.listLinePieces_tokens (indent + 8) body]
  | .matchSum scrutinee left leftBody right rightBody => by
      simp [InfixStmt.linePieces, InfixStmt.tokens, tokensOf_append, tokensOf_blanks, tokensOf,
        word, sym, space, Expr.tokensOf_pieces,
        InfixLeaf.listLinePieces_tokens (indent + 8) leftBody,
        InfixLeaf.listLinePieces_tokens (indent + 8) rightBody]

theorem InfixStmt.listLinePieces_tokens (indent : Nat) : (statements : List InfixStmt) →
    ((InfixStmt.listLinePieces indent statements).map tokensOf).flatten =
      InfixStmt.listTokens statements
  | [] => rfl
  | statement :: rest => by
      simp [InfixStmt.listLinePieces, InfixStmt.listTokens,
        InfixStmt.linePieces_tokens indent statement, InfixStmt.listLinePieces_tokens indent rest]

theorem InfixStmt.linePieces_separated (indent : Nat) : (statement : InfixStmt) →
    (∀ name ∈ statement.identifiers, ValidIdentifier name) →
    ∀ line ∈ statement.linePieces indent, Separated line
  | .leaf statement, valid, line, mem =>
      InfixLeaf.linePieces_separated indent statement valid line mem
  | .matchPair scrutinee first second body, valid, line, mem => by
      simp only [InfixStmt.linePieces, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      rcases mem with ((same | same) | mem) | same | same
      · subst same
        have scrutineePart := Expr.separated_append scrutinee
          (fun name mem => valid name (by simp [InfixStmt.identifiers, mem]))
          [sym ')', space, sym '{'] (Separated.cons_sym (by decide) (Separated.cons_space
            (sym_valid (by decide)))) (head_sym (by decide))
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_space (Separated.cons_sym (by decide) scrutineePart)) head_space)
      · subst same
        exact Separated.blanks_append (indent + 4) (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_space (Separated.cons_sym (by decide) (Separated.cons_word
            (valid first (by simp [InfixStmt.identifiers])) (Separated.cons_sym (by decide)
              (Separated.cons_space (Separated.cons_word
                (valid second (by simp [InfixStmt.identifiers]))
                (Separated.cons_sym (by decide) (Separated.cons_space (sym_valid (by decide))))
                (head_sym (by decide))))) (head_sym (by decide))))) head_space)
      · exact InfixLeaf.listLinePieces_separated (indent + 8) body
          (fun name mem => valid name (by simp [InfixStmt.identifiers, mem])) line mem
      · subst same
        exact Separated.blanks_append (indent + 4) (sym_valid (by decide))
      · subst same
        exact Separated.blanks_append indent (sym_valid (by decide))
  | .matchSum scrutinee left leftBody right rightBody, valid, line, mem => by
      simp only [InfixStmt.linePieces, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      rcases mem with (((((same | same) | mem) | same | same) | mem) | same | same)
      · subst same
        have scrutineePart := Expr.separated_append scrutinee
          (fun name mem => valid name (by simp [InfixStmt.identifiers, mem]))
          [sym ')', space, sym '{'] (Separated.cons_sym (by decide) (Separated.cons_space
            (sym_valid (by decide)))) (head_sym (by decide))
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        exact Separated.blanks_append indent (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_space (Separated.cons_sym (by decide) scrutineePart)) head_space)
      · subst same
        exact Separated.blanks_append (indent + 4) (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_space (Separated.cons_word (keyword_valid (by decide))
            (Separated.cons_sym (by decide) (Separated.cons_word
              (valid left (by simp [InfixStmt.identifiers])) (Separated.cons_sym (by decide)
                (Separated.cons_space (sym_valid (by decide)))) (head_sym (by decide))))
            (head_sym (by decide)))) head_space)
      · exact InfixLeaf.listLinePieces_separated (indent + 8) leftBody
          (fun name mem => valid name (by simp [InfixStmt.identifiers, mem])) line mem
      · subst same
        exact Separated.blanks_append (indent + 4) (sym_valid (by decide))
      · subst same
        exact Separated.blanks_append (indent + 4) (Separated.cons_word (keyword_valid (by decide))
          (Separated.cons_space (Separated.cons_word (keyword_valid (by decide))
            (Separated.cons_sym (by decide) (Separated.cons_word
              (valid right (by simp [InfixStmt.identifiers])) (Separated.cons_sym (by decide)
                (Separated.cons_space (sym_valid (by decide)))) (head_sym (by decide))))
            (head_sym (by decide)))) head_space)
      · exact InfixLeaf.listLinePieces_separated (indent + 8) rightBody
          (fun name mem => valid name (by simp [InfixStmt.identifiers, mem])) line mem
      · subst same
        exact Separated.blanks_append (indent + 4) (sym_valid (by decide))
      · subst same
        exact Separated.blanks_append indent (sym_valid (by decide))

theorem InfixStmt.listLinePieces_separated (indent : Nat) : (statements : List InfixStmt) →
    (∀ name ∈ InfixStmt.listIdentifiers statements, ValidIdentifier name) →
    ∀ line ∈ InfixStmt.listLinePieces indent statements, Separated line
  | [], _, _, mem => by simp [InfixStmt.listLinePieces] at mem
  | statement :: rest, valid, line, mem => by
      simp only [InfixStmt.listLinePieces, List.mem_append] at mem
      rcases mem with mem | mem
      · exact InfixStmt.linePieces_separated indent statement
          (fun name found => valid name (by simp [InfixStmt.listIdentifiers, found])) line mem
      · exact InfixStmt.listLinePieces_separated indent rest
          (fun name found => valid name (by simp [InfixStmt.listIdentifiers, found])) line mem

/-- The pieces of `SourceFile.linePieces`, with the generic functions before
the ordinary ones and an infix method body. -/
def GenericFile.linePieces (file : GenericFile) : List (List Piece) :=
  [[word "import", space, sym '*', space, word "from", space, word "std", sym ';'],
    [word "import", space, sym '*', space, word "from", space, word "std", sym '.',
      word "dispatch", sym ';']] ++
  aliasImportLinePieces file.opcodeAliases ++ [[]] ++
  file.generics.flatMap GenericDecl.linePieces ++
  file.functions.flatMap FunctionDecl.linePieces ++
  [[word "contract", space, word file.contract, space, sym '{'],
    blanks 4 ++ [word "function", space, word file.method.name, sym '('] ++
      parameterPieces file.method.parameters ++
      [sym ')', space, word "public", space, word "returns", space, sym '(', word "uint256",
        sym ')', space, sym '{']] ++
  InfixStmt.listLinePieces 8 file.method.body ++
  [blanks 8 ++ [word "return", space] ++ file.method.result.pieces ++ [sym ';'],
    blanks 4 ++ [sym '}'], [sym '}']]

theorem generics_lines_toList (generics : List GenericDecl) :
    (generics.flatMap GenericDecl.lines).map String.toList =
      (generics.flatMap GenericDecl.linePieces).map render := by
  induction generics with
  | nil => rfl
  | cons declaration rest ih =>
      simp only [List.flatMap_cons, List.map_append, ih, GenericDecl.lines_toList]

theorem generics_linePieces_tokens (generics : List GenericDecl) :
    ((generics.flatMap GenericDecl.linePieces).map tokensOf).flatten =
      generics.flatMap GenericDecl.tokens := by
  induction generics with
  | nil => rfl
  | cons declaration rest ih =>
      simp only [List.flatMap_cons, List.map_append, List.flatten_append, ih,
        GenericDecl.linePieces_tokens]

theorem GenericFile.lines_toList (file : GenericFile) :
    file.lines.map String.toList = file.linePieces.map render := by
  simp only [GenericFile.lines, GenericFile.linePieces, List.map_append, aliasImportLines_toList,
    generics_lines_toList, functions_lines_toList]
  simp [InfixStmt.listLines_toList, parameterText_toList, Expr.print_toList, render_append,
    render_blanks, render, Piece.chars, Token.chars, word, sym, space]

theorem GenericFile.linePieces_tokens (file : GenericFile) :
    (file.linePieces.map tokensOf).flatten = file.tokens := by
  simp only [GenericFile.linePieces, GenericFile.tokens, List.map_append, List.flatten_append,
    aliasImportLinePieces_tokens, generics_linePieces_tokens, functions_linePieces_tokens]
  simp [importTokens, signatureTokens, InfixStmt.listLinePieces_tokens, parameterPieces_tokens,
    Expr.tokensOf_pieces, tokensOf_append, tokensOf_blanks, tokensOf, word, sym, space]

/-- Every identifier of the generic file is lexically valid. -/
def GenericFile.IdentifiersValid (file : GenericFile) : Prop :=
  (∀ alias ∈ file.opcodeAliases, ValidIdentifier alias.1 ∧ ValidIdentifier alias.2) ∧
    (∀ declaration ∈ file.generics, ∀ name ∈ declaration.identifiers, ValidIdentifier name) ∧
    (∀ function ∈ file.functions, ∀ name ∈ function.identifiers, ValidIdentifier name) ∧
    ValidIdentifier file.contract ∧ ValidIdentifier file.method.name ∧
    (∀ parameter ∈ file.method.parameters, ValidIdentifier parameter) ∧
    (∀ name ∈ InfixStmt.listIdentifiers file.method.body, ValidIdentifier name) ∧
    (∀ name ∈ file.method.result.identifiers, ValidIdentifier name)

/-- The generic file without its generic functions and method body. Its lines
are the generic file's other lines. -/
def GenericFile.skeleton (file : GenericFile) : SourceFile where
  opcodeAliases := file.opcodeAliases
  functions := file.functions
  contract := file.contract
  method := {
    name := file.method.name, parameters := file.method.parameters, body := [],
    result := file.method.result }

theorem GenericFile.linePieces_separated (file : GenericFile) (valid : file.IdentifiersValid) :
    ∀ line ∈ file.linePieces, Separated line := by
  obtain ⟨aliasesValid, genericsValid, functionsValid, contractValid, methodValid,
    parametersValid, bodyValid, resultValid⟩ := valid
  have skeleton := file.skeleton.linePieces_separated ⟨aliasesValid, functionsValid,
    contractValid, methodValid, parametersValid,
    by simp [GenericFile.skeleton, Stmt.listIdentifiers], resultValid⟩
  intro line mem
  unfold GenericFile.linePieces at mem
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
          · exact skeleton line (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_left _ (List.mem_append_left _ mem))))
          · obtain ⟨declaration, declarationMem, lineMem⟩ := List.mem_flatMap.mp mem
            exact GenericDecl.linePieces_separated declaration
              (genericsValid declaration declarationMem) line lineMem
        · exact skeleton line (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_right _ mem))))
      · exact skeleton line (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ mem)))
    · exact InfixStmt.listLinePieces_separated 8 file.method.body bodyValid line mem
  · exact skeleton line (List.mem_append_right _ mem)

theorem GenericFile.print_toList (file : GenericFile) :
    file.print.toList = render (joinLines file.linePieces) := by
  rw [GenericFile.print, String.toList_append, String.toList_intercalate, joinLines,
    render_append, render_intercalate, GenericFile.lines_toList]
  rfl

/-- **Text round trip.** The printed text of a generic file with lexically
valid, non-reserved names parses back to that file. -/
theorem parseGenericSource_print (file : GenericFile) (names : file.NamesOk)
    (valid : file.IdentifiersValid) : parseGenericSource file.print = some file := by
  rw [parseGenericSource, GenericFile.print_toList,
    lex_render (joinLines_separated _ (file.linePieces_separated valid)), Option.bind_some,
    tokensOf_joinLines, GenericFile.linePieces_tokens]
  exact parseGenericFile_tokens file names

/-- The meaning of a printed generic file's text is the meaning of the file. -/
theorem genericSourceCall_print (file : GenericFile) (names : file.NamesOk)
    (valid : file.IdentifiersValid) (method : String) (arguments : List Nat) :
    genericSourceCall file.print method arguments = file.call method arguments := by
  simp [genericSourceCall, parseGenericSource_print file names valid]

/-! ### Loop-free files -/

theorem SourceFile.toGeneric_namesOk (file : SourceFile) (names : file.NamesOk) :
    file.toGeneric.NamesOk := by
  obtain ⟨functionsOk, contractOk, methodOk, parametersOk, bodyOk, resultOk⟩ := names
  unfold GenericFile.NamesOk
  refine ⟨fun _ absent => by simp [SourceFile.toGeneric] at absent, functionsOk, contractOk,
    methodOk, parametersOk, ?_, ?_, resultOk⟩
  · intro name mem
    simp only [SourceFile.toGeneric, InfixStmt.listIdentifiers_toInfix] at mem
    exact bodyOk name mem
  · intro statement mem
    simp only [SourceFile.toGeneric, List.mem_map] at mem
    obtain ⟨original, _, rfl⟩ := mem
    cases original <;> trivial

theorem SourceFile.toGeneric_valid (file : SourceFile) (valid : file.IdentifiersValid) :
    file.toGeneric.IdentifiersValid := by
  obtain ⟨aliasesValid, functionsValid, contractValid, methodValid, parametersValid, bodyValid,
    resultValid⟩ := valid
  unfold GenericFile.IdentifiersValid
  refine ⟨aliasesValid, fun _ absent => by simp [SourceFile.toGeneric] at absent,
    functionsValid, contractValid, methodValid, parametersValid, ?_, resultValid⟩
  intro name mem
  simp only [SourceFile.toGeneric, InfixStmt.listIdentifiers_toInfix] at mem
  exact bodyValid name mem

/-- **Agreement on loop-free files.** Read as a generic program, the printed
text of a loop-free file with valid, non-reserved names has its `sourceCall`
meaning. -/
theorem genericSourceCall_print_loopFree (file : SourceFile) (names : file.NamesOk)
    (valid : file.IdentifiersValid) (method : String) (arguments : List Nat) :
    genericSourceCall file.print method arguments = sourceCall file.print method arguments := by
  have generic := genericSourceCall_print file.toGeneric (file.toGeneric_namesOk names)
    (file.toGeneric_valid valid) method arguments
  rw [SourceFile.toGeneric_print] at generic
  rw [generic, sourceCall_print file names valid, SourceFile.toGeneric_call]

end Solcore.Synthesis.Source.ScalarMeaning
