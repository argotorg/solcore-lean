import Solcore.Core.Internal.Renaming
import Solcore.Frontend.RustHull.LoweringSupport
import Solcore.Frontend.RustHull.Effects
import Solcore.Core.Machine
import Solcore.Frontend.RustHull.Syntax

/-!
# Hull lowering

The compiler from Hull and inline Yul to Core. Main declarations: `lowerExpression`, `lowerBuiltin`,
`lowerStatement`, `lowerFunction`, `assemble`, `YulLowering.lowerExpr`.
-/

section
-- leanmerge: from Solcore.Frontend.RustYulPrimitives
/-! Pure inline-Yul operations lowered to the existing Core language.
The operation names follow solcore-rs commit
`e2eef19409fc8879cd4a9cc342ed60e3152f72c0`. Arguments are evaluated from
right to left, once each, before the operation. Comparisons produce EVM words.
Memory, storage, calls and termination belong to the enclosing effect lowering.
-/

set_option autoImplicit false

namespace Solcore.Frontend.RustYulPrimitives

open Core

inductive Error where
  | unknownBuiltin (name : String)
  | wrongArity (name : String) (expected actual : Nat)
  deriving Repr, BEq, DecidableEq

structure Lowered where
  type : Ty
  expression : Expr
  deriving Repr, BEq, DecidableEq

private structure Operation where
  arity : Nat
  resultType : Ty
  /-- The nearest variables contain arguments in source order. -/
  body : Expr

private def asWord (condition : Expr) : Expr :=
  .ifE condition (.word (Word.ofNatModulo 1)) (.word Word.zero)

private def binary (operation : BinaryOp) : Operation :=
  ⟨2, .word, .binary operation (.var 0) (.var 1)⟩

private def comparison (operation : BinaryOp) : Operation :=
  ⟨2, .word, asWord (.binary operation (.var 0) (.var 1))⟩

private def reversedComparison (operation : BinaryOp) : Operation :=
  ⟨2, .word, asWord (.binary operation (.var 1) (.var 0))⟩

private def shift (operation : BinaryOp) : Operation :=
  -- Yul takes (distance, value); Core takes (value, distance).
  ⟨2, .word, .binary operation (.var 1) (.var 0)⟩

private def operation? (name : String) : Option Operation :=
  match name with
  | "add" => some (binary .wordAdd)
  | "sub" => some (binary .wordSub)
  | "mul" => some (binary .wordMul)
  | "div" => some (binary .wordDiv)
  | "mod" => some (binary .wordMod)
  | "sdiv" => some (binary .wordSdiv)
  | "smod" => some (binary .wordSmod)
  | "exp" => some (binary .wordPow)
  | "signextend" => some (binary .wordSignExtend)
  | "lt" => some (reversedComparison .wordGt)
  | "gt" => some (comparison .wordGt)
  | "slt" => some (reversedComparison .wordSgt)
  | "sgt" => some (comparison .wordSgt)
  | "eq" => some (comparison .wordEq)
  | "iszero" => some ⟨1, .word, asWord (.binary .wordEq (.var 0) (.word Word.zero))⟩
  | "and" => some (binary .wordAnd)
  | "or" => some (binary .wordOr)
  | "xor" => some (binary .wordXor)
  | "not" => some ⟨1, .word, .unary .wordNot (.var 0)⟩
  | "byte" => some (binary .wordByte)
  | "shl" => some (shift .wordShl)
  | "shr" => some (shift .wordShr)
  | "sar" => some (shift .wordSar)
  | "clz" => some ⟨1, .word, .unary .wordClz (.var 0)⟩
  | "addmod" => some ⟨3, .word, .ternary .wordAddMod (.var 0) (.var 1) (.var 2)⟩
  | "mulmod" => some ⟨3, .word, .ternary .wordMulMod (.var 0) (.var 1) (.var 2)⟩
  | "pop" => some ⟨1, .unit, .unit⟩
  | _ => none

/-- Check whether a name belongs to the pure EVM operation fragment. -/
def supports (name : String) : Bool := (operation? name).isSome

private def bindArguments (resultType : Ty) (body : Expr) : Nat → List Expr → Expr
  | _, [] => body
  | depth, argument :: rest =>
      -- Typed lambda binders also require `pop`'s discarded input to be a word.
      .apply (.lambda .word resultType (bindArguments resultType body (depth + 1) rest))
        (argument.rename fun index => index + depth)

/-- Build ordinary Core code, with explicit arity and unknown-name errors.
The enclosing compiler checks the result in its lexical Core context. Every
argument is a typed word binder, including discarded `pop` arguments. -/
def compile (name : String) (arguments : List Expr) : Except Error Lowered := do
  let operation ← match operation? name with
    | some operation => pure operation
    | none => throw (.unknownBuiltin name)
  unless arguments.length = operation.arity do
    throw (.wrongArity name operation.arity arguments.length)
  pure ⟨operation.resultType,
    bindArguments operation.resultType operation.body 0 arguments.reverse⟩

end Solcore.Frontend.RustYulPrimitives
end

section
-- leanmerge: from Solcore.Frontend.RustHull.YulLowering
/-! Inline Yul lowers into the same Core cells, sums and loop closures as Hull.
Language failures propagate before later argument or statement effects. Yul
locals are words and their lexical scope ends with the enclosing assembly block.
-/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.YulLowering

private def decodeChars : List Char → Option (List Char)
  | [] => some []
  | '\\' :: escaped :: rest => do
      let char ← match escaped with
        | '"' => some '"' | '\\' => some '\\' | 'n' => some '\n' | 't' => some '\t'
        | _ => none
      return char :: (← decodeChars rest)
  | '\\' :: [] | '"' :: _ => none
  | char :: rest => return char :: (← decodeChars rest)

private def stringWord (text : String) : LowerM Core.Word := do
  let chars ← match text.toList with
    | '"' :: rest => match rest.reverse with
      | '"' :: inner => match decodeChars inner.reverse with
        | some chars => pure chars
        | none => fail "invalid inline Yul string escape"
      | _ => fail "missing closing quote in inline Yul string"
    | _ => fail "missing opening quote in inline Yul string"
  let bytes := (String.ofList chars).toUTF8
  if bytes.size > 32 then fail "inline Yul string literal exceeds one EVM word"
  else
    let encoded := bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0
    pure (Core.Word.ofNatModulo (encoded * 256 ^ (32 - bytes.size)))

def literalWord : YulLit → LowerM Core.Word
  | .number text | .hex text => parseWord text
  | .bool value => pure (Core.Word.ofNatModulo (if value then 1 else 0))
  | .string text => stringWord text

def bindArguments (resultType : Core.Ty) (body : Core.Expr) :
    Nat → List Lowered → Core.Expr
  | _, [] => body
  | depth, argument :: rest =>
      Core.LanguageResult.bind resultType
        (argument.expression.rename fun index => index + depth)
        (bindArguments resultType body (depth + 1) rest)

structure FunctionBinding where
  signature : Signature
  index : Nat

structure FunctionDecl where
  name : YulName
  parameters : List YulName
  returns : List YulName
  body : List YulStmt

def FunctionDecl.signature (function : FunctionDecl) : Signature :=
  ⟨function.name.name, function.parameters.map (fun _ => .word),
    bundleType (function.returns.map (fun _ => .word))⟩

structure Context where
  scope : Scope
  functions : List FunctionBinding := []
  returnSlots : Option (List Nat) := none
  hullFunctions : List Signature := []

def Context.push (context : Context) (binding : Binding) : Context := {
  scope := binding :: context.scope
  functions := context.functions.map fun entry => {entry with index := entry.index + 1}
  returnSlots := context.returnSlots.map (List.map (· + 1))
  hullFunctions := context.hullFunctions
}

def Context.temporary (context : Context) (type : Core.Ty) : Context :=
  context.push ⟨none, type, false⟩

def Context.addLocal (context : Context) (name : String) : Context :=
  context.push ⟨some name, .word, true⟩

def Context.hideValues (context : Context) : Context := {
  context with scope := context.scope.map fun binding =>
    if binding.name.any (·.startsWith "$lean$evm$") then binding else {binding with name := none}
               returnSlots := none
}

def readReturn (context : Context) : LowerM Lowered := do
  let slots ← match context.returnSlots with
    | some slots => pure slots
    | none => fail "inline Yul leave is outside a local function"
  pure (packArguments (slots.map fun index =>
    ⟨.word, Core.OptionalCell.read .word (.var index) (Core.Word.ofNatModulo 1)⟩))

/-- Explicit upstream `usr$` calls refer to Hull functions. Word arguments and
Word/Unit results have identical Hull and Yul layouts. Other layouts need a
separate flattening bridge and are rejected before generating a Core call. -/
def lowerHullCall (context : Context) (name : YulName)
    (arguments : List Lowered) : LowerM Lowered := do
  let hullName := (name.name.drop 4).toString
  let signature ← match context.hullFunctions.find? (·.name == hullName) with
    | some signature => pure signature
    | none => fail s!"unknown Hull function in inline Yul: {name.name}" name.span
  unless signature.parameters.all (· == .word) do
    fail s!"inline Yul Hull call {name.name} requires Word parameters; aggregate, Bool and Unit parameters need layout conversion" name.span
  unless signature.result == .word || signature.result == .unit do
    fail s!"inline Yul Hull call {name.name} requires a Word or Unit result; aggregate and Bool results need layout conversion" name.span
  unless signature.parameters.length = arguments.length do
    fail s!"inline Yul Hull call {name.name}: expected {signature.parameters.length} arguments, received {arguments.length}" name.span
  let function ← context.scope.read (Effects.slotName ("function$" ++ hullName))
  expectType signature.functionType function.type
  let rawArguments := (List.range arguments.length).map Core.Expr.var
  let body := Core.LanguageResult.bind signature.result
    (function.expression.rename fun index => index + arguments.length)
    (.apply (.var 0) ((bundle rawArguments).weakenAt 0))
  pure ⟨signature.result, bindArguments signature.result body 0 arguments.reverse⟩

def lowerExpr : Nat → Context → YulExpr → LowerM Lowered
  | 0, _, expression => fail "inline Yul expression depth exhausted" expression.span
  | fuel + 1, context, expression => do
      match expression.kind with
      | .literal value =>
          pure ⟨.word, Core.LanguageResult.success (.word (← literalWord value))⟩
      | .ident name =>
          if name.name.startsWith Effects.reservedPrefix then
            fail "reserved runtime binding name in inline Yul" name.span
          let value ← context.scope.read name.name
          expectType .word value.type
          pure value
      | .call name arguments =>
          if name.name.startsWith Effects.reservedPrefix then
            fail "reserved runtime function name in inline Yul" name.span
          let lowered ← arguments.mapM (lowerExpr fuel context)
          for argument in lowered do expectType .word argument.type
          let rawArguments := (List.range lowered.length).map Core.Expr.var
          match context.functions.find? (·.signature.name == name.name) with
          | some function =>
              unless function.signature.parameters.length = lowered.length do
                fail s!"inline Yul function {name.name}: expected {function.signature.parameters.length} arguments, received {lowered.length}" expression.span
              let body := Core.LanguageResult.bind function.signature.result
                (Core.OptionalCell.read function.signature.functionType
                  (.var (function.index + lowered.length)) (Core.Word.ofNatModulo 1))
                (.apply (.var 0) ((bundle rawArguments).weakenAt 0))
              pure ⟨function.signature.result,
                bindArguments function.signature.result body 0 lowered.reverse⟩
          | none =>
              if name.name.startsWith "usr$" then lowerHullCall context name lowered
              else if context.hullFunctions.any (·.name == name.name) then
                fail s!"plain-name Hull call has no defined upstream Yul target: {name.name}; use the explicit usr$ prefix" name.span
              else if Effects.supports name.name then
                let effectScope := lowered.foldl (fun scope _ => scope.temporary .word) context.scope
                let effect ← Effects.lowerBuiltin effectScope name.name rawArguments
                pure ⟨effect.type, bindArguments effect.type effect.expression 0 lowered.reverse⟩
              else
                let primitive ← match RustYulPrimitives.compile name.name rawArguments with
                  | .ok value => pure value
                  | .error error => fail s!"inline Yul primitive: {reprStr error}" expression.span
                pure ⟨primitive.type, bindArguments primitive.type
                  (Core.LanguageResult.success primitive.expression) 0 lowered.reverse⟩

/-- Standalone expressions have no local-function declarations. -/
def lowerExpression (fuel : Nat) (scope : Scope) (expression : YulExpr) : LowerM Lowered :=
  lowerExpr fuel {scope} expression

def condition (value : Lowered) : LowerM Core.Expr := do
  expectType .word value.type
  pure (Core.LanguageResult.bind .bool value.expression
    (Core.LanguageResult.success
      (.unary .boolNot (.binary .wordEq (.var 0) (.word Core.Word.zero)))))

def switchBranches : List (Core.Word × Core.Expr) → Core.Expr → Core.Expr
  | [], defaultBody => defaultBody.weakenAt 0
  | (value, body) :: rest, defaultBody =>
      .ifE (.binary .wordEq (.var 0) (.word value))
        (body.weakenAt 0) (switchBranches rest defaultBody)

def resultTypeFor (names : List YulName) : Core.Ty :=
  bundleType (names.map (fun _ => .word))

def distinctNames (names : List YulName) : Bool :=
  let texts := names.map (·.name)
  texts.eraseDups.length = texts.length

def allocateValues (names : List YulName) (body : Core.Expr) : Core.Expr :=
  names.zipIdx.foldr (fun (_, index) continuation =>
    .letE (Core.OptionalCell.allocateInitialized .word
      (projectArgument index names.length (.var index))) continuation) body

def allocateZeroes (names : List YulName) (body : Core.Expr) : Core.Expr :=
  names.foldr (fun _ continuation =>
    .letE (Core.OptionalCell.allocateInitialized .word (.word Core.Word.zero)) continuation) body

def assignMany (context : Context) (names : List YulName) (value : Lowered)
    (resultType : Core.Ty) (next : Core.Expr) : LowerM Core.Expr := do
  if names.isEmpty then fail "inline Yul assignment has no targets"
  else
    expectType (resultTypeFor names) value.type
    let writes ← names.zipIdx.mapM fun (name, sourceIndex) => do
      if name.name.startsWith Effects.reservedPrefix then
        fail "reserved runtime assignment target in inline Yul" name.span
      let (binding, index) ← context.scope.lookup name.name
      unless binding.reference do fail s!"inline Yul assignment to immutable binding: {name.name}" name.span
      expectType .word binding.type
      pure (Core.Expr.storeCell (.var (index + 1))
        (.inRight .unit (projectArgument sourceIndex names.length (.var 0))))
    let body := writes.foldr (fun write continuation =>
      .letE write (continuation.weakenAt 0)) (next.weakenAt 0)
    pure (Core.LanguageResult.bind (Core.LocalLoop.controlType resultType) value.expression body)

def declarations (statements : List YulStmt) : LowerM (List FunctionDecl) := do
  let functions := statements.filterMap fun statement => match statement.kind with
    | .functionDef name parameters returns body => some ⟨name, parameters, returns, body⟩
    | _ => none
  unless distinctNames (functions.map (·.name)) do fail "duplicate inline Yul function declaration"
  for function in functions do
    for name in function.name :: function.parameters ++ function.returns do
      if name.name.startsWith Effects.reservedPrefix then
        fail "reserved runtime function binding in inline Yul" name.span
    unless distinctNames (function.parameters ++ function.returns) do
      fail s!"duplicate inline Yul parameter or return name: {function.name.name}" function.name.span
  pure functions

def addFunctions (context : Context) (functions : List FunctionDecl) : Context :=
  let allocated := functions.foldl (fun current function =>
    current.temporary (Core.OptionalCell.referenceType function.signature.functionType)) context
  {allocated with functions := functions.zipIdx.map (fun (function, index) =>
    ⟨function.signature, functions.length - 1 - index⟩) ++ allocated.functions}

mutual

def lowerSequence : Nat → Context → Core.Ty → Bool → List YulStmt →
    (Context → LowerM Core.Expr) → LowerM Core.Expr
  | 0, _, _, _, _, _ => fail "inline Yul statement depth exhausted"
  | fuel + 1, context, resultType, inLoop, statements, finish => do
      match statements with
      | [] => finish context
      | statement :: rest =>
          let next := fun context => lowerSequence fuel context resultType inLoop rest finish
          let block := fun context inLoop body => lowerBlock fuel context resultType inLoop body
            (fun _ => pure (Core.LocalLoop.fallthrough resultType))
          match statement.kind with
          | .letDecl names initializer =>
              if names.isEmpty then fail "inline Yul declaration has no names" statement.span
              else if !distinctNames names then fail "duplicate inline Yul declaration name" statement.span
              else
                for name in names do
                  if name.name.startsWith Effects.reservedPrefix then
                    fail "reserved runtime local name in inline Yul" name.span
                match initializer with
                | none =>
                    let inner := names.foldl (fun current name => current.addLocal name.name) context
                    pure (allocateZeroes names (← next inner))
                | some expression =>
                    let value ← lowerExpr fuel context expression
                    expectType (resultTypeFor names) value.type
                    let inner := names.foldl (fun current name => current.addLocal name.name)
                      (context.temporary value.type)
                    let continuation ← next inner
                    pure (Core.LanguageResult.bind (Core.LocalLoop.controlType resultType)
                      value.expression (allocateValues names continuation))
          | .assign names expression =>
              let value ← lowerExpr fuel context expression
              assignMany context names value resultType (← next context)
          | .expression expression =>
              let value ← lowerExpr fuel context expression
              expectType .unit value.type
              pure (Core.LocalSequence.discard (Core.LocalLoop.controlType resultType)
                value.expression (← next context))
          | .block body =>
              pure (Core.LocalLoop.sequence resultType (← block context inLoop body) (← next context))
          | .ifThen cond body =>
              let cond ← condition (← lowerExpr fuel context cond)
              let branch ← block context inLoop body
              pure (Core.LocalLoop.sequence resultType
                (Core.LocalLoop.conditional resultType cond branch (Core.LocalLoop.fallthrough resultType))
                (← next context))
          | .forLoop initializer cond post body =>
              let loop ← lowerBlock fuel context resultType false initializer fun loopContext => do
                let cond ← condition (← lowerExpr fuel loopContext cond)
                let body ← block loopContext true body
                let post ← block loopContext false post
                pure (Core.LocalLoop.iterate resultType cond body post (Core.Word.ofNatModulo 1))
              pure (Core.LocalLoop.sequence resultType loop (← next context))
          | .switch value cases defaultBody =>
              let value ← lowerExpr fuel context value
              expectType .word value.type
              let branches ← cases.mapM fun arm => do
                return (← literalWord arm.lit, ← block context inLoop arm.body)
              let keys := branches.map Prod.fst
              unless keys.eraseDups.length = keys.length do
                fail "duplicate inline Yul switch case" statement.span
              let defaultBody ← block context inLoop (defaultBody.getD [])
              let selected := Core.LanguageResult.bind (Core.LocalLoop.controlType resultType)
                value.expression (switchBranches branches defaultBody)
              pure (Core.LocalLoop.sequence resultType selected (← next context))
          | .breakStmt =>
              if inLoop then pure (Core.LocalLoop.breaking resultType)
              else fail "inline Yul break is outside a loop body" statement.span
          | .continueStmt =>
              if inLoop then pure (Core.LocalLoop.continuing resultType)
              else fail "inline Yul continue is outside a loop body" statement.span
          | .functionDef .. => next context
          | .leave =>
              let returned ← readReturn context
              expectType resultType returned.type
              pure (Core.LocalLoop.returnValue resultType returned.expression)

def lowerBlock : Nat → Context → Core.Ty → Bool → List YulStmt →
    (Context → LowerM Core.Expr) → LowerM Core.Expr
  | 0, _, _, _, _, _ => fail "inline Yul block depth exhausted"
  | fuel + 1, context, resultType, inLoop, statements, finish => do
      let functions ← declarations statements
      let inner := addFunctions context functions
      let closures ← functions.mapM (lowerFunction fuel inner)
      let body ← lowerSequence fuel inner resultType inLoop statements finish
      let installed := (closures.zipIdx).foldr (fun (closure, index) continuation =>
        Core.Expr.letE (.storeCell (.var (functions.length - 1 - index)) (.inRight .unit closure))
          (continuation.weakenAt 0)) body
      pure (functions.foldr (fun function continuation =>
        .letE (Core.OptionalCell.allocate function.signature.functionType) continuation) installed)

def lowerFunction : Nat → Context → FunctionDecl → LowerM Core.Expr
  | 0, _, function => fail "inline Yul function depth exhausted" function.name.span
  | fuel + 1, context, function => do
      let parameterType := bundleType function.signature.parameters
      let parameterContext := function.parameters.foldl (fun current name => current.addLocal name.name)
        (context.hideValues.temporary parameterType)
      let returnContext := function.returns.foldl (fun current name => current.addLocal name.name)
        parameterContext
      let slots := (List.range function.returns.length).map fun index => function.returns.length - 1 - index
      let returnContext := {returnContext with returnSlots := some slots}
      let resultType := function.signature.result
      let control ← lowerBlock fuel returnContext resultType false function.body fun finalContext => do
        let returned ← readReturn finalContext
        pure (Core.LocalLoop.returnValue resultType returned.expression)
      let body := Core.LocalControl.finish resultType
        (Core.LocalLoop.toControl resultType control (Core.Word.ofNatModulo 2))
        (Core.LanguageResult.failure resultType (.word (Core.Word.ofNatModulo 2)))
      pure (.lambda parameterType (Core.LanguageResult.resultType resultType)
        (allocateValues function.parameters (allocateZeroes function.returns body)))

end

private def validateControl : Nat → Bool → Bool → List YulStmt → LowerM Unit
  | 0, _, _, _ => fail "inline Yul control validation depth exhausted"
  | fuel + 1, inLoop, inFunction, statements => do
      for statement in statements do
        match statement.kind with
        | .breakStmt | .continueStmt =>
            unless inLoop do fail "inline Yul loop transfer is outside a loop body" statement.span
        | .leave =>
            unless inFunction do fail "inline Yul leave is outside a local function" statement.span
        | .block body | .ifThen _ body => validateControl fuel inLoop inFunction body
        | .forLoop initializer _ post body =>
            validateControl fuel false inFunction initializer
            validateControl fuel true inFunction body
            validateControl fuel false inFunction post
        | .switch _ cases defaultBody =>
            for arm in cases do validateControl fuel inLoop inFunction arm.body
            validateControl fuel inLoop inFunction (defaultBody.getD [])
        | .functionDef _ _ _ body => validateControl fuel false true body
        | _ => pure ()

/-- Assemble lexical inline Yul functions and statements using the common Core
machine. Function bodies resolve only their own values and lexical functions. -/
def lowerStatements (fuel : Nat) (scope : Scope) (resultType : Core.Ty)
    (statements : List YulStmt) (hullFunctions : List Signature := []) : LowerM Core.Expr := do
  -- Check even statements after `leave`: reachability cannot make malformed
  -- transfers legal or connect an inner function's break to an outer loop.
  validateControl fuel false false statements
  lowerBlock fuel {scope, hullFunctions} resultType false statements
    (fun _ => pure (Core.LocalLoop.fallthrough resultType))

end Solcore.Frontend.RustHull.YulLowering
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Lowering
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.YulFragment
/-! The inline Yul the common recursive proof accepts: statement lists of `let`
with one name, assignment to one name, expression statements, nested blocks,
`if` and `switch` without string case literals, over literals, variables and
calls of supported names or of the connected word primitives. Effect layers
that support no name accept no block. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.YulFragment

/-- The connected word primitives, lowered as pure Core operations. -/
def primitives : List String := ["add", "sub", "lt", "gt", "eq", "iszero"]

mutual
  inductive ExpressionEligible (supported : String → Prop) : YulExpr → Prop where
    | literal {value : YulLit} {span : Option Span} : ExpressionEligible supported ⟨.literal value, span⟩
    | ident {name : YulName} {span : Option Span} : ExpressionEligible supported ⟨.ident name, span⟩
    | call {name : YulName} {arguments : List YulExpr} {span : Option Span}
        (named : supported name.name ∨ name.name ∈ primitives) (eligible : ArgumentsEligible supported arguments) :
        ExpressionEligible supported ⟨.call name arguments, span⟩

  inductive ArgumentsEligible (supported : String → Prop) : List YulExpr → Prop where
    | nil : ArgumentsEligible supported []
    | cons {argument : YulExpr} {rest : List YulExpr} (head : ExpressionEligible supported argument)
        (tail : ArgumentsEligible supported rest) : ArgumentsEligible supported (argument :: rest)
end

inductive StatementEligible (supported : String → Prop) : YulStmt → Prop where
  | letValue {name : YulName} {value : YulExpr} {span : Option Span} (eligible : ExpressionEligible supported value) :
      StatementEligible supported ⟨.letDecl [name] (some value), span⟩
  | letZero {name : YulName} {span : Option Span} : StatementEligible supported ⟨.letDecl [name] none, span⟩
  | assign {name : YulName} {value : YulExpr} {span : Option Span} (eligible : ExpressionEligible supported value) :
      StatementEligible supported ⟨.assign [name] value, span⟩
  | expression {value : YulExpr} {span : Option Span} (eligible : ExpressionEligible supported value) :
      StatementEligible supported ⟨.expression value, span⟩
  | block {body : List YulStmt} {span : Option Span}
      (eligible : ∀ statement ∈ body, StatementEligible supported statement) :
      StatementEligible supported ⟨.block body, span⟩
  | ifThen {condition : YulExpr} {body : List YulStmt} {span : Option Span}
      (tested : ExpressionEligible supported condition)
      (eligible : ∀ statement ∈ body, StatementEligible supported statement) :
      StatementEligible supported ⟨.ifThen condition body, span⟩
  | switch {value : YulExpr} {cases : List YulCase} {defaultBody : Option (List YulStmt)} {span : Option Span}
      (scrutinee : ExpressionEligible supported value) (literals : ∀ arm ∈ cases, ∀ text, arm.lit ≠ .string text)
      (arms : ∀ arm ∈ cases, ∀ statement ∈ arm.body, StatementEligible supported statement)
      (defaults : ∀ statement ∈ defaultBody.getD [], StatementEligible supported statement) :
      StatementEligible supported ⟨.switch value cases defaultBody, span⟩

def Eligible (supported : String → Prop) (body : List YulStmt) : Prop :=
  (∃ name, supported name) ∧ ∀ statement ∈ body, StatementEligible supported statement

theorem Eligible.empty {body : List YulStmt} (eligible : Eligible (fun _ => False) body) : False := by
  obtain ⟨⟨_, impossible⟩, _⟩ := eligible
  exact impossible

end Solcore.Frontend.RustHull.YulFragment
end
