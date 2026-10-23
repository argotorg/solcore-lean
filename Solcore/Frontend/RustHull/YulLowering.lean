import Solcore.Frontend.RustHull.LoweringSupport
import Solcore.Frontend.RustYulPrimitives
import Solcore.Frontend.RustHull.Effects

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

private def bindArguments (resultType : Core.Ty) (body : Core.Expr) :
    Nat → List Lowered → Core.Expr
  | _, [] => body
  | depth, argument :: rest =>
      Core.LanguageResult.bind resultType
        (argument.expression.rename fun index => index + depth)
        (bindArguments resultType body (depth + 1) rest)

private structure FunctionBinding where
  signature : Signature
  index : Nat

private structure FunctionDecl where
  name : YulName
  parameters : List YulName
  returns : List YulName
  body : List YulStmt

private def FunctionDecl.signature (function : FunctionDecl) : Signature :=
  ⟨function.name.name, function.parameters.map (fun _ => .word),
    bundleType (function.returns.map (fun _ => .word))⟩

private structure Context where
  scope : Scope
  functions : List FunctionBinding := []
  returnSlots : Option (List Nat) := none
  hullFunctions : List Signature := []

private def Context.push (context : Context) (binding : Binding) : Context := {
  scope := binding :: context.scope
  functions := context.functions.map fun entry => {entry with index := entry.index + 1}
  returnSlots := context.returnSlots.map (List.map (· + 1))
  hullFunctions := context.hullFunctions
}

private def Context.temporary (context : Context) (type : Core.Ty) : Context :=
  context.push ⟨none, type, false⟩

private def Context.addLocal (context : Context) (name : String) : Context :=
  context.push ⟨some name, .word, true⟩

private def Context.hideValues (context : Context) : Context := {
  context with scope := context.scope.map fun binding =>
    if binding.name.any (·.startsWith "$lean$evm$") then binding else {binding with name := none}
               returnSlots := none
}

private def readReturn (context : Context) : LowerM Lowered := do
  let slots ← match context.returnSlots with
    | some slots => pure slots
    | none => fail "inline Yul leave is outside a local function"
  pure (packArguments (slots.map fun index =>
    ⟨.word, Core.OptionalCell.read .word (.var index) (Core.Word.ofNatModulo 1)⟩))

/-- Explicit upstream `usr$` calls refer to Hull functions. Word arguments and
Word/Unit results have identical Hull and Yul layouts. Other layouts need a
separate flattening bridge and are rejected before generating a Core call. -/
private def lowerHullCall (context : Context) (name : YulName)
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

private def lowerExpr : Nat → Context → YulExpr → LowerM Lowered
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

private def condition (value : Lowered) : LowerM Core.Expr := do
  expectType .word value.type
  pure (Core.LanguageResult.bind .bool value.expression
    (Core.LanguageResult.success
      (.unary .boolNot (.binary .wordEq (.var 0) (.word Core.Word.zero)))))

private def switchBranches : List (Core.Word × Core.Expr) → Core.Expr → Core.Expr
  | [], defaultBody => defaultBody.weakenAt 0
  | (value, body) :: rest, defaultBody =>
      .ifE (.binary .wordEq (.var 0) (.word value))
        (body.weakenAt 0) (switchBranches rest defaultBody)

private def resultTypeFor (names : List YulName) : Core.Ty :=
  bundleType (names.map (fun _ => .word))

private def distinctNames (names : List YulName) : Bool :=
  let texts := names.map (·.name)
  texts.eraseDups.length = texts.length

private def allocateValues (names : List YulName) (body : Core.Expr) : Core.Expr :=
  names.zipIdx.foldr (fun (_, index) continuation =>
    .letE (Core.OptionalCell.allocateInitialized .word
      (projectArgument index names.length (.var index))) continuation) body

private def allocateZeroes (names : List YulName) (body : Core.Expr) : Core.Expr :=
  names.foldr (fun _ continuation =>
    .letE (Core.OptionalCell.allocateInitialized .word (.word Core.Word.zero)) continuation) body

private def assignMany (context : Context) (names : List YulName) (value : Lowered)
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

private def declarations (statements : List YulStmt) : LowerM (List FunctionDecl) := do
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

private def addFunctions (context : Context) (functions : List FunctionDecl) : Context :=
  let allocated := functions.foldl (fun current function =>
    current.temporary (Core.OptionalCell.referenceType function.signature.functionType)) context
  {allocated with functions := functions.zipIdx.map (fun (function, index) =>
    ⟨function.signature, functions.length - 1 - index⟩) ++ allocated.functions}

mutual

private def lowerSequence : Nat → Context → Core.Ty → Bool → List YulStmt →
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

private def lowerBlock : Nat → Context → Core.Ty → Bool → List YulStmt →
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

private def lowerFunction : Nat → Context → FunctionDecl → LowerM Core.Expr
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
