import Solcore.Frontend.RustHull.LoweringSupport
import Solcore.Frontend.RustHull.YulLowering
import Solcore.Frontend.RustYulPrimitives
import Solcore.Core.Machine

/-! Imported Hull executes on the ordinary Core machine. The importer is not a
certificate for the upstream compiler: annotations, bindings, calls and the
generated closed Core term are checked independently here. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull

def boolLike (type : Core.Ty) : Bool :=
  type == .bool || type == .sum .unit .unit

def boolean (type : Core.Ty) (condition : Core.Expr) : LowerM Core.Expr :=
  if type = .bool then pure condition
  else if type = .sum .unit .unit then
    pure (.ifE condition (.inRight .unit .unit) (.inLeft .unit .unit))
  else fail "expected a boolean or a sum of two Unit types"

def condition (value : Lowered) : LowerM Core.Expr := do
  if value.type = .bool then pure value.expression
  else if value.type = .sum .unit .unit then
    pure (Core.LanguageResult.bind .bool value.expression
      (.caseE (.var 0) (Core.LanguageResult.success (.bool false))
        (Core.LanguageResult.success (.bool true))))
  else fail "condition is not boolean"

def primitiveName : String → String
  | "primAddWord" | "integerAdd" => "add"
  | "subWord" | "integerSub" => "sub"
  | "mulWord" | "integerMul" => "mul"
  | "primEqWord" | "integerEq" => "eq"
  | "gtWord" => "gt"
  | "integerLt" => "lt"
  | "bxorWord" => "xor"
  | "bandWord" => "and"
  | "borWord" => "or"
  | "bnotWord" => "not"
  | name => name

def lowerBuiltin (scope : Scope) (name : String) (expected : Core.Ty)
    (arguments : List Lowered) : LowerM Lowered := do
  let packed := packArguments arguments
  let raw := (List.range arguments.length).map fun index =>
    projectArgument index arguments.length (.var 0)
  if Effects.supports name then
    for argument in arguments do expectType .word argument.type
    let lowered ← Effects.lowerBuiltin (scope.temporary packed.type) name raw
    expectType expected lowered.type
    pure ⟨expected, Core.LanguageResult.bind expected packed.expression lowered.expression⟩
  else if name = "wordToInteger" || name = "wordFromInteger" then
    unless arguments.length = 1 do fail s!"wrong arity for {name}"
    expectType .word packed.type
    expectType .word expected
    pure packed
  else if name = "iszero" then
    unless arguments.length = 1 && boolLike packed.type do
      fail "Hull iszero expects one boolean value"
    let input ← condition packed
    let value ← boolean expected (.unary .boolNot (.var 0))
    pure ⟨expected, Core.LanguageResult.bind expected input
      (Core.LanguageResult.success value)⟩
  else
    for argument in arguments do expectType .word argument.type
    let operation := primitiveName name
    let lowered ← (RustYulPrimitives.compile operation raw).mapError fun error =>
      ⟨s!"unsupported Hull call {name}: {reprStr error}", none⟩
    let comparisons := ["lt", "gt", "slt", "sgt", "eq"]
    let value ← if operation ∈ comparisons then
        boolean expected (.unary .boolNot
          (.binary .wordEq lowered.expression (.word Core.Word.zero)))
      else do
        expectType expected lowered.type
        pure lowered.expression
    pure ⟨expected, Core.LanguageResult.bind expected packed.expression
      (Core.LanguageResult.success value)⟩

def inject (index : Nat) : Core.Ty → Core.Ty → Core.Expr → LowerM Core.Expr
  | .sum left right, payload, value =>
      if index = 0 then do
        expectType left payload
        pure (.inLeft right value)
      else return .inRight left (← inject (index - 1) right payload value)
  | target, payload, value => do
      unless index = 0 do fail "sum injection index is out of range"
      expectType target payload
      pure value

def lowerExpression : Nat → List Signature → Scope → Expr → LowerM Lowered
  | 0, _, _, _ => fail "Hull expression lowering depth exhausted"
  | fuel + 1, signatures, scope, expression => do
      let expected ← lowerType (fuel + 1) expression.ty
      let result ← match expression.kind with
        | .word text => pure ⟨.word, Core.LanguageResult.success (.word (← parseWord text))⟩
        | .bool value => pure ⟨expected, Core.LanguageResult.success (← boolean expected (.bool value))⟩
        | .unit => pure ⟨.unit, Core.LanguageResult.success .unit⟩
        | .var name =>
            if name.startsWith Effects.reservedPrefix then fail "reserved runtime binding name"
            else scope.read name
        | .pair left right => do
            let left ← lowerExpression fuel signatures scope left
            let right ← lowerExpression fuel signatures scope right
            pure ⟨.product left.type right.type,
              Core.LocalSequence.pair left.type right.type left.expression right.expression⟩
        | .fst value | .snd value => do
            let value ← lowerExpression fuel signatures scope value
            let (left, right) ← match value.type with
              | .product left right => pure (left, right)
              | _ => fail "projection operand is not a product"
            let (type, projected) := match expression.kind with
              | .fst _ => (left, Core.Expr.first (.var 0))
              | _ => (right, Core.Expr.second (.var 0))
            pure ⟨type, Core.LanguageResult.bind type value.expression
              (Core.LanguageResult.success projected)⟩
        | .inl target value | .inr target value => do
            let target ← lowerType fuel target
            let value ← lowerExpression fuel signatures scope value
            let (left, right) ← match target with
              | .sum left right => pure (left, right)
              | _ => fail "injection target is not a sum"
            let injected ← match expression.kind with
              | .inl _ _ => do expectType left value.type; pure (Core.Expr.inLeft right (.var 0))
              | _ => do expectType right value.type; pure (Core.Expr.inRight left (.var 0))
            pure ⟨target, Core.LanguageResult.bind target value.expression
              (Core.LanguageResult.success injected)⟩
        | .inK index target value => do
            let target ← lowerType fuel target
            let value ← lowerExpression fuel signatures scope value
            let injected ← inject index target value.type (.var 0)
            pure ⟨target, Core.LanguageResult.bind target value.expression
              (Core.LanguageResult.success injected)⟩
        | .call name args => do
            let args ← args.mapM (lowerExpression fuel signatures scope)
            match signatures.find? (·.name == name) with
            | none => lowerBuiltin scope name expected args
            | some signature => do
                unless args.length = signature.parameters.length do fail s!"wrong arity for {name}"
                for (argument, parameter) in args.zip signature.parameters do
                  expectType parameter argument.type
                -- Hull keeps function names separate from local value names.
                let function ← scope.read (Effects.slotName ("function$" ++ name))
                expectType signature.functionType function.type
                let packed := packArguments args
                pure ⟨signature.result,
                  Core.LanguageResult.bind signature.result function.expression
                    (Core.LanguageResult.bind signature.result (packed.expression.weakenAt 0)
                      (.apply (.var 1) (.var 0)))⟩
        | .ifThen target cond thenExpr elseExpr => do
            let target ← lowerType fuel target
            let cond ← condition (← lowerExpression fuel signatures scope cond)
            let yes ← lowerExpression fuel signatures scope thenExpr
            let no ← lowerExpression fuel signatures scope elseExpr
            expectType target yes.type
            expectType target no.type
            pure ⟨target, Core.LocalControl.choose target cond yes.expression no.expression⟩
      expectType expected result.type
      pure result

def place : Nat → Expr → LowerM (String × List Bool)
  | 0, _ => fail "place depth exhausted"
  | fuel + 1, expression => match expression.kind with
    | .var name => pure (name, [])
    | .fst value => do let (name, path) ← place fuel value; pure (name, path ++ [false])
    | .snd value => do let (name, path) ← place fuel value; pure (name, path ++ [true])
    | _ => fail "assignment requires a local or product projection"

def updateProduct : List Bool → Core.Ty → Core.Expr → Core.Expr → LowerM Core.Expr
  | [], _, _, value => pure value
  | direction :: rest, .product left right, old, value =>
      if direction then return .pair (.first old) (← updateProduct rest right (.second old) value)
      else return .pair (← updateProduct rest left (.first old) value) (.second old)
  | _ :: _, _, _, _ => fail "assignment projection is not a product"

/-- Return a pure Option-like payload test for one match arm. -/
def testPattern (type : Core.Ty) (pattern : PatKind) : LowerM (Core.Ty × (Core.Expr → Core.Expr)) := do
  match pattern with
  | .wildcard | .var _ => pure (type, fun value => .inRight .unit value)
  | .intLit text =>
      expectType .word type
      let word ← parseWord text
      pure (.word, fun value => .ifE (.binary .wordEq value (.word word))
        (.inRight .unit value) (.inLeft .word .unit))
  | .con .inl => match type with
      | .sum left _ => pure (left, fun value => .caseE value (.inRight .unit (.var 0)) (.inLeft left .unit))
      | _ => fail "inl pattern requires a sum"
  | .con .inr => match type with
      | .sum _ right => pure (right, fun value => .caseE value (.inLeft right .unit) (.inRight .unit (.var 0)))
      | _ => fail "inr pattern requires a sum"
  | .con (.inK index) =>
      let rec test (remaining : Nat) (type : Core.Ty) : LowerM (Core.Ty × (Core.Expr → Core.Expr)) :=
        match type with
        | .sum left right => if remaining = 0 then
            pure (left, fun value => .caseE value (.inRight .unit (.var 0)) (.inLeft left .unit))
          else do
            let (payload, nested) ← test (remaining - 1) right
            pure (payload, fun value => .caseE value (.inLeft payload .unit) (nested (.var 0)))
        | type => if remaining = 0 then pure (type, fun value => .inRight .unit value)
          else fail "sum pattern index is out of range"
      test index type

mutual
  def lowerStatements : Nat → List Signature → Scope → Core.Ty → Nat → List Stmt → LowerM Core.Expr
    | 0, _, _, _, _, _ => fail "Hull statement lowering depth exhausted"
    | fuel + 1, signatures, scope, result, loops, statements => do
        match statements with
        | [] => pure (Core.LocalLoop.fallthrough result)
        | statement :: rest =>
            match statement.kind with
            | .letDecl name type =>
                if name.startsWith Effects.reservedPrefix then fail "reserved runtime local name"
                let type ← lowerType fuel type
                let zero ← zeroValue type
                let body ← lowerStatements fuel signatures (scope.addLocal name type) result loops rest
                pure (.letE (Core.OptionalCell.allocateInitialized type zero) body)
            | _ =>
                let first ← lowerStatement fuel signatures scope result loops statement
                let next ← lowerStatements fuel signatures scope result loops rest
                pure (Core.LocalLoop.sequence result first next)

  def lowerStatement : Nat → List Signature → Scope → Core.Ty → Nat → Stmt → LowerM Core.Expr
    | 0, _, _, _, _, _ => fail "Hull statement lowering depth exhausted"
    | fuel + 1, signatures, scope, result, loops, statement => do
        match statement.kind with
        | .letDecl name type => lowerStatements fuel signatures scope result loops [⟨.letDecl name type, statement.span⟩]
        | .assign lhs rhs =>
            -- Check every annotation on the lvalue as well as its actual place.
            let left ← lowerExpression fuel signatures scope lhs
            let right ← lowerExpression fuel signatures scope rhs
            expectType left.type right.type
            let (name, path) ← place fuel lhs
            let (binding, index) ← scope.lookup name
            unless binding.reference do fail "cannot assign a temporary value"
            let updated ← updateProduct path binding.type (.var 0) (.var 1)
            pure (Core.LanguageResult.bind (Core.LocalLoop.controlType result) right.expression
              (Core.LanguageResult.bind (Core.LocalLoop.controlType result)
                (Core.OptionalCell.read binding.type (.var (index + 1)) (Core.Word.ofNatModulo 1))
                (.letE (.storeCell (.var (index + 2)) (.inRight .unit updated))
                  (Core.LocalLoop.fallthrough result))))
        | .expression value =>
            let value ← lowerExpression fuel signatures scope value
            pure (Core.LocalSequence.discard (Core.LocalLoop.controlType result)
              value.expression (Core.LocalLoop.fallthrough result))
        | .returnStmt value =>
            let value ← lowerExpression fuel signatures scope value
            expectType result value.type
            pure (Core.LocalLoop.returnValue result value.expression)
        | .block body => lowerStatements fuel signatures scope result loops body
        | .forLoop init cond post body =>
            if !init.isEmpty then
              lowerStatements fuel signatures scope result loops
                (init ++ [⟨.forLoop [] cond post body, statement.span⟩])
            else do
              let cond ← condition (← lowerExpression fuel signatures scope cond)
              let body ← lowerStatements fuel signatures scope result (loops + 1) body
              let post ← lowerStatements fuel signatures scope result (loops + 1) post
              pure (Core.LocalLoop.iterate result cond body post (Core.Word.ofNatModulo 3))
        | .breakStmt =>
            if loops = 0 then fail "break outside a loop" statement.span
            else pure (Core.LocalLoop.breaking result)
        | .continueStmt =>
            if loops = 0 then fail "continue outside a loop" statement.span
            else pure (Core.LocalLoop.continuing result)
        | .matchStmt target value alts =>
            let target ← lowerType fuel target
            let value ← lowerExpression fuel signatures scope value
            expectType target value.type
            let arms ← lowerAlternatives fuel signatures (scope.temporary target) result loops target alts
            pure (Core.LanguageResult.bind (Core.LocalLoop.controlType result) value.expression arms)
        | .assembly body => YulLowering.lowerStatements fuel scope result body signatures
        | .revert message =>
            let exit ← Effects.revertMessage scope message
            pure (Core.LocalSequence.discard (Core.LocalLoop.controlType result)
              exit (Core.LocalLoop.fallthrough result))
        | .comment _ => pure (Core.LocalLoop.fallthrough result)

  def lowerAlternatives : Nat → List Signature → Scope → Core.Ty → Nat → Core.Ty → List Alt → LowerM Core.Expr
    | 0, _, _, _, _, _, _ => fail "Hull match lowering depth exhausted"
    | fuel + 1, signatures, scope, result, loops, target, alts => do
        match alts with
        | [] => pure (Core.LocalLoop.fallthrough result)
        | alt :: rest =>
            if alt.binder.startsWith Effects.reservedPrefix then fail "reserved runtime match binder"
            let (payload, test) ← testPattern target alt.pat.kind
            let body ← lowerStatements fuel signatures
              ((scope.temporary payload).addLocal alt.binder payload) result loops alt.body
            let next ← lowerAlternatives fuel signatures scope result loops target rest
            pure (.caseE (test (.var 0)) (next.weakenAt 0)
              (.letE (Core.OptionalCell.allocateInitialized payload (.var 0)) body))
end

structure Compiled where
  entry : String
  parameters : List Core.Ty
  result : Core.Ty
  /-- A closed Core function taking the packed input arguments. -/
  expression : Core.Expr
  deriving Repr

def signature (fuel : Nat) (function : Function) : LowerM Signature := do
  if function.name.startsWith Effects.reservedPrefix then fail "reserved runtime function name"
  pure ⟨function.name, ← function.args.mapM (fun arg => lowerType fuel arg.ty),
    ← lowerType fuel function.ret⟩

def lowerFunction (fuel : Nat) (signatures : List Signature)
    (scope : Scope) (function : Function) (own : Signature) : LowerM Core.Expr := do
  unless (function.args.map (·.name)).eraseDups.length = function.args.length do
    fail s!"duplicate parameter in {function.name}"
  for argument in function.args do
    if argument.name.startsWith Effects.reservedPrefix then fail "reserved runtime parameter name"
  let parameterScope := (function.args.zip own.parameters).foldl
    (fun scope (arg, type) => scope.addLocal arg.name type)
    (scope.temporary (bundleType own.parameters))
  let statements ← lowerStatements fuel signatures parameterScope own.result 0 function.body
  let fallback := if own.result = .unit then Core.LanguageResult.success .unit
    else Core.LanguageResult.failure own.result (.word (Core.Word.ofNatModulo 4))
  let body := Core.LocalControl.finish own.result
    (Core.LocalLoop.toControl own.result statements (Core.Word.ofNatModulo 5)) fallback
  let body := own.parameters.zipIdx.foldr (fun (type, index) body =>
    .letE (Core.OptionalCell.allocateInitialized type
      (projectArgument index own.parameters.length (.var index))) body) body
  pure (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body)

/-- Assemble function cells in an existing runtime scope followed by the raw
input bundle. The caller allocates this scope and checks the closed term. -/
def assemble (functions : List Function) (entry : String) (runtime : Scope)
    (fuel : Nat := 4096) : LowerM (Signature × Core.Expr) := do
  unless (functions.map (·.name)).eraseDups.length = functions.length do
    fail "duplicate Hull function name"
  let signatures ← functions.mapM (signature fuel)
  let own ← match signatures.find? (·.name == entry) with
    | some signature => pure signature
    | none => fail s!"missing Hull entry: {entry}"
  let globals := signatures.reverse
  let scope : Scope := (globals.map fun signature =>
    ⟨some (Effects.slotName ("function$" ++ signature.name)), signature.functionType, true⟩) ++ runtime
  let closures ← (functions.zip signatures).reverse.mapM fun (function, signature) =>
    lowerFunction fuel signatures scope function signature
  let (_, index) ← scope.lookup (Effects.slotName ("function$" ++ entry))
  let invoke := Core.LanguageResult.bind own.result
    (Core.OptionalCell.read own.functionType (.var index) (Core.Word.ofNatModulo 1))
    (.apply (.var 0) (.var (globals.length + runtime.length + 1)))
  let installed : Core.Expr := closures.zipIdx.foldr (fun (closure, index) next =>
    .letE (.storeCell (.var index) (.inRight .unit closure)) (next.weakenAt 0)) invoke
  let allocated : Core.Expr := signatures.foldr (fun signature next =>
    .letE (Core.OptionalCell.allocate signature.functionType) next) installed
  pure (own, allocated)

/-- Compile a selected exported top-level Hull entry. Unsupported object effects
are diagnosed by their own entry compiler, never silently erased here. -/
def compile (program : Program) (entry : String) (fuel : Nat := 4096) : LowerM Compiled := do
  unless entry ∈ program.entryPoints do fail s!"entry is not exported by Hull: {entry}"
  let (own, allocated) ← assemble program.functions entry [] fuel
  let expression := Core.Expr.lambda (bundleType own.parameters)
    (Core.LanguageResult.resultType own.result) allocated
  let inferred ← (Core.inferDetailed [] [] expression).mapError fun error =>
    ⟨s!"Core validation: {reprStr error}", none⟩
  expectType own.functionType inferred
  pure ⟨entry, own.parameters, own.result, expression⟩

end Solcore.Frontend.RustHull
