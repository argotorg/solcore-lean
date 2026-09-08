import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TypedLetReturnBodyEmbeddingProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties

/-! Parsed typed prefixes retain original initializer scopes and exact ordered
Core without argument values. Runtime entries now use this static adapter;
the old tree boundary remains narrower, including for nominal inputs. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owners : List Resolved.DeclarationId :=
  [⟨⟨.main, ⟨[⟨"TypedPrefixes", by decide⟩], by decide⟩⟩, 17⟩,
    ⟨⟨.main, ⟨[⟨"OtherPrefixes", by decide⟩], by decide⟩⟩, 41⟩]
private def types : TypeNameTable := [(["Opaque"], .namedData ⟨91⟩), (["Alias"], .namedData ⟨91⟩),
  (["Word"], .word), (["Bool"], .bool), (["Unit"], .unit), (["Cell"], .cell .word),
  (["Fn"], .function .word (.namedData ⟨91⟩)), (["Pkg", "Token"], .namedData ⟨92⟩),
  (["Pkg.Token"], .word), (["Opaque"], .bool)]

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-typed-prefixes.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"lexer invariant: {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"parser invariant: {reprStr error}")

private def declaredInputs (source : Syntax.FunctionDecl) (owner : Resolved.DeclarationId)
    (expected : List (String × Core.Ty)) : IO LocalTypeInputs := do
  let parameters := source.value.signature.parameters.elements
  let written := parameters.filterMap fun parameter => match parameter.value with
    | .typed none name annotation => (interpretTypeName? types annotation).map (name.value, ·)
    | _ => none
  assertTrue (decide (written = expected ∧ parameters.length = expected.length))
    "source parameter spelling, annotation or order changed"
  match accepted : declareRuntimeParameters? types owner parameters with
  | none => throw (IO.userError "value-free parameter declaration failed")
  | some inputs =>
      have _ := declareRuntimeParameters?_sound accepted
      assertTrue (decide (inputs.names.map Prod.fst = (expected.map Prod.fst).reverse ∧
        inputs.context.values = (expected.map Prod.snd).reverse ∧ inputs.ids =
          (List.range expected.length).reverse.map (fun index => (⟨owner, index⟩ : Resolved.LocalId))))
        "parameter-only input rows lost exact source positions"
      return inputs

private theorem excludeWrong {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Block} {core wrong : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnBodyElaborates types owner inputs source core type)
    (different : wrong ≠ core) : ¬ TypedLetReturnBodyElaborates types owner inputs source wrong type :=
  fun other => different (other.result_unique elaboration).1

private def compatibility (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (body : Syntax.Block) : IO Unit := do
  match body with
  | ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =>
      have _ := elaborateTypedLetReturnBody?_single types owner inputs returned blockSpan returnSpan
      assertTrue (decide (elaborateTypedLetReturnBody? types owner inputs body =
        elaborateReturnBody? inputs.names inputs.context body)) "singleton full Option equality changed"
  | ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ =>
      have _ := elaborateTypedLetReturnBody?_conditional types owner inputs condition thenBody elseBody blockSpan ifSpan
      assertTrue (decide (elaborateTypedLetReturnBody? types owner inputs body =
        elaborateTerminalReturnTree? inputs.names inputs.context body)) "conditional full Option equality changed"
      match thenBody, elseBody with
      | ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩,
          ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩ =>
          have _ := elaborateTypedLetReturnBody?_conditional_singletons types owner inputs condition thenReturned elseReturned
            blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan
          assertTrue (decide (elaborateTypedLetReturnBody? types owner inputs body =
            elaborateConditionalReturnBody? inputs.names inputs.context body)) "old conditional lost a full optional result"
      | _, _ => pure ()
  | _ => pure ()
  match old : elaborateTerminalReturnTree? inputs.names inputs.context body with
  | none => pure ()
  | some _ =>
      let elaboration := elaborateTerminalReturnTree?_elaborates old
      have _ := elaboration.typedLetReturnBody types owner
      have _ := elaboration.hasType.typedLetReturnBody types owner
      have _ := elaboration.typedLetReturnBody_complete types owner
      pure ()

private def inspectPrefix (owner : Resolved.DeclarationId) (blockSpan : Syntax.SourceSpan)
    (statements : List Syntax.Statement) (inputs : LocalTypeInputs) (core : Core.Expr)
    (returnType : Core.Ty) (nextIndex : Nat) (names : List String) : IO Unit := do
  match statements, names, core with
  | ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest,
      expectedName :: expectedRest, .letE initializerCore tailCore =>
      if checked : elaborateTypedLetReturnBody? types owner inputs
          ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ =
            some (.letE initializerCore tailCore, returnType) then
        have _ := elaborateTypedLetReturnBody?_binding_children checked
        pure ()
      else throw (IO.userError "actual binding lost its complete child evidence")
      let some type := interpretTypeName? types annotation
        | throw (IO.userError "retained let annotation lost its first-match meaning")
      assertTrue (decide (name.value = expectedName ∧ name.value ∉ inputs.names.map Prod.fst ∧
        elaborateLocalExpression? inputs.names inputs.context initializer = some (initializerCore, type)))
        "initializer was moved into its new scope, reordered, or disagreed with its annotation"
      assertTrue (blockSpan.contains letSpan && letSpan.contains name.span &&
        letSpan.contains annotation.span && letSpan.contains initializer.span &&
        decide (name.span.endByte ≤ annotation.span.startByte ∧ annotation.span.endByte ≤ initializer.span.startByte))
        "original let child spans or written order changed"
      let extended := inputs.bindFresh owner name.value type
      assertTrue (decide (extended.ids = (⟨owner, nextIndex⟩ : Resolved.LocalId) :: inputs.ids ∧
        extended.names = (name.value, ⟨owner, nextIndex⟩) :: inputs.names ∧
        extended.context = (⟨owner, nextIndex⟩, type) :: inputs.context ∧
        elaborateTypedLetReturnBody? types owner extended ⟨blockSpan, rest⟩ = some (tailCore, returnType)))
        "fresh row or already-extended tail was changed or weakened twice"
      inspectPrefix owner blockSpan rest extended tailCore returnType (nextIndex + 1) expectedRest
  | _, [], _ =>
      assertTrue (decide (elaborateTerminalReturnTree? inputs.names inputs.context ⟨blockSpan, statements⟩ =
        some (core, returnType))) "complete terminal suffix did not retain exact Core"
  | _, _, _ => throw (IO.userError "source prefix and independently expected Core have different shapes")
termination_by statements.length

private def accepted (content : String) (parameters : List (String × Core.Ty))
    (prefixNames : List String) (expected : Core.Expr) (type : Core.Ty) : IO Unit := do
  let some source ← parsed? (Syntax.Parser.functionDecl .module) content
    | throw (IO.userError s!"positive function did not completely parse: {content}")
  for owner in owners do
    let inputs ← declaredInputs source owner parameters
    assertTrue (decide (interpretRuntimeFunctionHeader? types source.value.signature = some type))
      "entry rejection contrast was caused by its header"
    match result : elaborateTypedLetReturnBody? types owner inputs source.value.body with
    | none => throw (IO.userError s!"valid finite typed prefix was rejected: {content}")
    | some (core, actualType) =>
        let elaboration := elaborateTypedLetReturnBody?_elaborates result
        let typing := elaborateTypedLetReturnBody?_sound result
        have _ := elaborateTypedLetReturnBody?_iff.mp result
        have _ := elaboration.complete
        have _ := elaboration.hasType
        have _ := typing.elaborates_exact
        have _ := typing.elaborates
        have _ := typing.type_unique typing
        have _ := typedLetReturnBodyHasType_iff_elaborates_exact.mp typing
        have _ := typedLetReturnBodyHasType_iff_elaborates.mp typing
        have _ := elaborateTypedLetReturnBody?_core_hasType result
        assertTrue (decide (core = expected ∧ actualType = type ∧ Core.infer? inputs.context.values core = some type))
          "exact ordered let Core, nominal type or original free positions changed"
        let wrong := Core.Expr.ifE (.bool true) core core
        if different : wrong ≠ core then
          have _ := excludeWrong elaboration different
          assertTrue (decide (Core.infer? inputs.context.values wrong = some type))
            "non-provenance comparison was not independently equally typed"
        else throw (IO.userError "wrong-Core contrast became identical")
        inspectPrefix owner source.value.body.span source.value.body.value inputs core type parameters.length prefixNames
        if prefixNames.isEmpty then
          assertTrue (decide (elaborateTerminalReturnTree? inputs.names inputs.context source.value.body = some (core, type) ∧
            (compileRuntimeFunction? types owner source).map (fun compiled => (compiled.core, compiled.returnType)) = some (core, type)))
            "zero-prefix compatibility changed the old whole result"
        else
          assertTrue ((elaborateTerminalReturnTree? inputs.names inputs.context source.value.body).isNone)
            "typed-prefix entry integration expanded the old tree adapter"
        assertTrue (decide ((compileRuntimeFunction? types owner source).map (fun compiled =>
          (compiled.core, compiled.returnType, compiled.inputs.names, compiled.inputs.context.values)) =
            some (expected, type, inputs.names, inputs.context.values))) "entry changed exact Core or original parameter-only rows"
    compatibility owner inputs source.value.body

private def repeated (count : Nat) (annotation : String) (type : Core.Ty) : IO Unit := do
  let indices := List.range count
  let prefixText := String.join (indices.map fun index =>
    s!"let z{index}: {annotation} = " ++ (if index = 0 then "x" else s!"z{index - 1}") ++ ";")
  let selected := if count = 0 then "x" else s!"z{count - 1}"
  let suffix := "if(c){if(c){return " ++ selected ++ ";}else{return y;}}else{return x;}"
  let terminal := Core.Expr.ifE (.var count)
    (.ifE (.var count) (.var (if count = 0 then 2 else 0)) (.var (count + 1))) (.var (count + 2))
  let core := indices.foldr (fun index tail => Core.Expr.letE (.var (if index = 0 then 2 else 0)) tail) terminal
  accepted (s!"function chain(x: {annotation},y: {annotation},c: Bool) returns ({annotation})" ++
    "{" ++ prefixText ++ suffix ++ "}") [("x", type), ("y", type), ("c", .bool)]
    (indices.map fun index => s!"z{index}") core type

private def rejected (body : String) : IO Unit := do
  let some source ← parsed? (Syntax.Parser.functionDecl .module)
      ("function rejected(x: Word,y: Word,c: Bool,q: Opaque,f: Fn) returns (Word)" ++ body)
    | throw (IO.userError s!"semantic rejection failed to completely parse: {body}")
  for owner in owners do
    let inputs ← declaredInputs source owner [("x", .word), ("y", .word), ("c", .bool), ("q", .namedData ⟨91⟩),
      ("f", .function .word (.namedData ⟨91⟩))]
    match failed : elaborateTypedLetReturnBody? types owner inputs source.value.body with
    | some _ => throw (IO.userError s!"whole typed-prefix rejection was bypassed: {body}")
    | none =>
        have _ := elaborateTypedLetReturnBody?_eq_none_iff.mp failed
        assertTrue (compileRuntimeFunction? types owner source).isNone "unsupported body changed the old entry"
    compatibility owner inputs source.value.body

private def dictionaryBoundary : IO Unit := do
  let some source ← parsed? (Syntax.Parser.functionDecl .module)
      "function meaning(x: Opaque) returns (Opaque){let z: Alias = x;return z;}"
    | throw (IO.userError "annotation contrast did not completely parse")
  for owner in owners do
    let inputs ← declaredInputs source owner [("x", .namedData ⟨91⟩)]
    let expected : Option (Core.Expr × Core.Ty) := some (.letE (.var 0) (.var 0), .namedData ⟨91⟩)
    assertTrue (decide (elaborateTypedLetReturnBody? types owner inputs source.value.body = expected ∧
      elaborateTypedLetReturnBody? (types ++ [(["Alias"], .word)]) owner inputs source.value.body = expected ∧
      elaborateTypedLetReturnBody? ((["Alias"], .word) :: types) owner inputs source.value.body = none))
      "let annotation ignored its first matching type meaning"
  let some annotation ← parsed? Syntax.Parser.typeExpr "Pkg /* qualified */ . Token"
    | throw (IO.userError "qualified annotation failed to parse")
  let .named name none := annotation.value | throw (IO.userError "qualified type changed shape")
  assertTrue (decide (qualifiedTypeNameKey name = ["Pkg", "Token"] ∧
    interpretTypeName? types annotation = some (.namedData ⟨92⟩) ∧ types.lookup? ["Pkg.Token"] = some .word))
    "qualified component spelling was flattened into a different key"

def frontendParsedTypedLetReturnBodyTests : IO Unit := do
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ =>
        simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for (annotation, type) in [("Opaque", Core.Ty.namedData ⟨91⟩), ("Word", .word), ("Bool", .bool),
      ("Unit", .unit), ("Cell", .cell .word), ("Fn", .function .word (.namedData ⟨91⟩)),
      ("Pkg.Token", .namedData ⟨92⟩)] do
    for count in [0, 1, 2, 5, 16, 40] do repeated count annotation type
  accepted "function ordered(x: Word) returns (Word){let y: Word = x;let z: Word = y - x;return z;}"
    [("x", .word)] ["y", "z"] (.letE (.var 0) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0))) .word
  accepted "function unused(x: Opaque){let z: Alias = x;return;}" [("x", .namedData ⟨91⟩)] ["z"]
    (.letE (.var 0) .unit) .unit
  accepted "function qualified(x: Pkg.Token) returns (Pkg.Token){let z: Pkg /* components */ . Token = x;return z;}"
    [("x", .namedData ⟨92⟩)] ["z"] (.letE (.var 0) (.var 0)) (.namedData ⟨92⟩)
  accepted "function mixed(x: Word,c: Bool) returns (Bool){let w: Word = x / (x + 1);let b: Bool = c && w < x;return b || !c;}"
    [("x", .word), ("c", .bool)] ["w", "b"]
    (.letE (.binary .wordDiv (.var 1) (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1))))
      (.letE (.ifE (.var 1) (Core.Expr.wordLt (.var 0) (.var 2)) (.bool false))
        (.ifE (.var 0) (.bool true) (.unary .boolNot (.var 2))))) .bool
  accepted "function constant() returns (Word){let z: Word = 7;return z;}" [] ["z"]
    (.letE (.word (Core.Word.ofNatModulo 7)) (.var 0)) .word
  accepted "function bare(){return;}" [] [] .unit .unit
  accepted "function old(c: Bool,x: Word) returns (Word){if(c){return x;}else{return x;}}"
    [("c", .bool), ("x", .word)] [] (.ifE (.var 1) (.var 0) (.var 0)) .word
  dictionaryBoundary
  rejected ("{let z: Word = " ++ toString (2 ^ 256 : Nat) ++ ";return x;}")
  for body in ["{let z = x;return z;}", "{let z: Word;return x;}", "{let z;return x;}",
      "{let z: Word = z;return x;}", "{let a: Word = b;let b: Word = x;return a;}",
      "{let x: Word = y;return x;}", "{let z: Word = x;let z: Word = y;return z;}",
      "{let z: Word = missing;return x;}", "{let z: Bool = x;return x;}",
      "{let z: Unknown = x;return x;}", "{let z: Word<Bool> = x;return x;}",
      "{let z: Pkg.Token = x;return x;}", "{let z: Opaque = c;return x;}",
      "{let z: Opaque = f(x);return x;}", "{let z: Word = (0 == 0) ? x : missing;return x;}",
      "{let z: Word = x;}", "{let z: Word = x;return z;return x;}",
      "{let z: Word = x;z = y;return z;}", "{let z: Word = x;{return z;}}",
      "{let z: Word = x;if(c){let a: Word = z;return a;}else{return z;}}",
      "{let z: Word = x;if(0 == 0){return z;}else{let a: Word = z;return a;}}",
      "{if(c){let z: Word = x;return z;}else{return y;}}",
      "{let z: Word = x;if(c){return z;}}", "{let z: Word = x;if(x){return z;}else{return y;}}",
      "{let z: Word = x;if(0 == 0){return z;}else{if(c){return y;}else{return missing;}}}",
      "{let z: Word = x;if(0 == 0){return z;}else{return c;}}",
      "{return missing;}", "{if(0 == 0){return x;}else{return missing;}}"] do rejected body
  for content in ["{let z: Word = ;return z;}", "{let z: Word = x return z;}",
      "{let z: Word = x;return z;", "{let z: Word = x;return z;} trailing"] do
    assertTrue (← parsed? (Syntax.Parser.block .allow) content).isNone "incomplete binding acquired static meaning"

end Tests
