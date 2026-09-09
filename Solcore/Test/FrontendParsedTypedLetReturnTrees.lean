import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TypedLetReturnTreeEmbeddingProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties

/-! Completely parsed alternating let/if trees are checked against independent
open Core. Siblings reuse their original scope and may reuse a fresh identity.
Value-free entry compilation keeps the original parameter-only rows. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owners : List Resolved.DeclarationId :=
  [⟨⟨.main, ⟨[⟨"RecursiveBindings", by decide⟩], by decide⟩⟩, 17⟩,
   ⟨⟨.main, ⟨[⟨"OtherBindings", by decide⟩], by decide⟩⟩, 41⟩]
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .word (.namedData ⟨91⟩)),
  (["Opaque"], .namedData ⟨91⟩), (["Alias"], .namedData ⟨91⟩), (["Opaque"], .bool),
  (["Pkg", "Token"], .namedData ⟨92⟩), (["Pkg.Token"], .word)]
private def parsed? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-recursive-bindings.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next => return if next.atEnd && next.diagnostics.isEmpty then some source else none
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "parser invariant")
private def declaredInputs (source : Syntax.FunctionDecl) (owner : Resolved.DeclarationId)
    (expected : List (String × Core.Ty)) : IO LocalTypeInputs := do
  let parameters := source.value.signature.parameters.elements
  let written ← parameters.mapM fun parameter => do
    let .typed none name annotation := parameter.value | throw (IO.userError "unexpected parameter shape")
    assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains annotation.span)
      "source parameter positions changed"
    let some type := interpretTypeName? types annotation | throw (IO.userError "parameter annotation rejected")
    pure (name.value, type)
  assertTrue (decide (written = expected)) "source spellings, annotations or order changed"
  match accepted : declareRuntimeParameters? types owner parameters with
  | none => throw (IO.userError "value-free declaration rejected")
  | some inputs =>
      have _ := declareRuntimeParameters?_sound accepted
      assertTrue (decide (inputs.names = (expected.zipIdx.map (fun (row, index) =>
        (row.1, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧ inputs.context.values = (expected.map Prod.snd).reverse))
        "original parameter identities or reversed type positions changed"
      return inputs
private theorem excludeWrong {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core wrong : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnTreeElaborates types owner inputs body core type) (different : wrong ≠ core) :
    ¬ TypedLetReturnTreeElaborates types owner inputs body wrong type :=
  fun other => different (other.result_unique elaboration).1
private def compatibility (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) (body : Syntax.Block) : IO Unit := do
  match old : elaborateTerminalReturnTree? inputs.names inputs.context body with
  | none => pure ()
  | some pair =>
      let elaboration := elaborateTerminalReturnTree?_elaborates old
      have _ := elaboration.typedLetReturnTree types owner
      have _ := elaboration.hasType.typedLetReturnTree types owner
      have _ := elaborateTypedLetReturnTree?_some_of_terminalReturnTree types owner old
      assertTrue (decide (elaborateTypedLetReturnTree? types owner inputs body = some pair)) "old tree success changed exact Core/type"
  match old : elaborateTypedLetReturnBody? types owner inputs body with
  | none => pure ()
  | some pair =>
      let elaboration := elaborateTypedLetReturnBody?_elaborates old
      have _ := elaboration.returnTree
      have _ := elaboration.hasType.returnTree
      have _ := elaborateTypedLetReturnTree?_some_of_typedLetReturnBody old
      assertTrue (decide (elaborateTypedLetReturnTree? types owner inputs body = some pair)) "old prefix success changed exact Core/type"
  match body with
  | ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =>
      have _ := elaborateTypedLetReturnTree?_single types owner inputs returned blockSpan returnSpan
      assertTrue (decide (elaborateTypedLetReturnTree? types owner inputs body =
        elaborateReturnBody? inputs.names inputs.context body)) "singleton full Option equality changed"
  | _ => pure ()
private def inspect (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) (body : Syntax.Block)
    (core : Core.Expr) (type : Core.Ty) (nextIndex : Nat) : IO Unit := do
  match body, core with
  | ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩, .letE initializerCore tailCore =>
      if checked : elaborateTypedLetReturnTree? types owner inputs
          ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ = some (.letE initializerCore tailCore, type) then
        have _ := elaborateTypedLetReturnTree?_binding_children checked
        pure ()
      else throw (IO.userError "binding lost exact child evidence")
      let some declaredType := interpretTypeName? types annotation | throw (IO.userError "binding annotation disappeared")
      assertTrue (decide (name.value ∉ inputs.names.map Prod.fst ∧
        elaborateLocalExpression? inputs.names inputs.context initializer = some (initializerCore, declaredType)) &&
        blockSpan.contains letSpan && letSpan.contains name.span && letSpan.contains annotation.span && letSpan.contains initializer.span &&
        decide (name.span.endByte ≤ annotation.span.startByte ∧ annotation.span.endByte ≤ initializer.span.startByte))
        "initializer changed its old scope, spelling, span or written order"
      let extended := inputs.bindFresh owner name.value declaredType
      assertTrue (decide (extended.ids = (⟨owner, nextIndex⟩ : Resolved.LocalId) :: inputs.ids ∧
        extended.names = (name.value, ⟨owner, nextIndex⟩) :: inputs.names ∧
        extended.context = (⟨owner, nextIndex⟩, declaredType) :: inputs.context)) "ancestor allocation or exact extended row changed"
      inspect owner extended ⟨blockSpan, rest⟩ tailCore type (nextIndex + 1)
  | ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩, .letE initializerCore tailCore =>
      let .identifier originalName := initializer.value | throw (IO.userError "inferred fixture expected original reference")
      let some inferredType := (inputs.names.lookup? originalName.value).bind inputs.context.lookup?
        | throw (IO.userError "original reference had no static type")
      if checked : elaborateTypedLetReturnTree? types owner inputs
          ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ = some (.letE initializerCore tailCore, type) then
        have _ := elaborateTypedLetReturnTree?_inferred_children checked
        pure ()
      else throw (IO.userError "inferred binding lost original child evidence")
      assertTrue (decide (name.value ∉ inputs.names.map Prod.fst ∧
        elaborateLocalExpression? inputs.names inputs.context initializer = some (initializerCore, inferredType)) &&
        blockSpan.contains letSpan && letSpan.contains name.span && letSpan.contains initializer.span &&
        decide (name.span.endByte ≤ initializer.span.startByte)) "inference rewrote annotation, scope or original spans"
      let extended := inputs.bindFresh owner name.value inferredType
      assertTrue (decide (extended.ids = (⟨owner, nextIndex⟩ : Resolved.LocalId) :: inputs.ids ∧
        extended.names = (name.value, ⟨owner, nextIndex⟩) :: inputs.names ∧
        extended.context = (⟨owner, nextIndex⟩, inferredType) :: inputs.context)) "inference changed fresh type or position"
      inspect owner extended ⟨blockSpan, rest⟩ tailCore type (nextIndex + 1)
  | ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩, .ifE conditionCore thenCore elseCore =>
      if checked : elaborateTypedLetReturnTree? types owner inputs
          ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ = some (.ifE conditionCore thenCore elseCore, type) then
        have _ := elaborateTypedLetReturnTree?_conditional_children checked
        pure ()
      else throw (IO.userError "conditional lost both original children")
      assertTrue (decide (elaborateLocalExpression? inputs.names inputs.context condition = some (conditionCore, .bool)) &&
        blockSpan.contains ifSpan && ifSpan.contains condition.span && ifSpan.contains thenBody.span && ifSpan.contains elseBody.span &&
        decide (thenBody.span.endByte ≤ elseBody.span.startByte)) "condition scope or ordered branch spans changed"
      match thenBody.value, elseBody.value with
      | ⟨_, .letDecl leftName (some leftAnnotation) _⟩ :: _, ⟨_, .letDecl rightName (some rightAnnotation) _⟩ :: _ =>
          let some leftType := interpretTypeName? types leftAnnotation | throw (IO.userError "left annotation lost")
          let some rightType := interpretTypeName? types rightAnnotation | throw (IO.userError "right annotation lost")
          assertTrue (decide ((inputs.bindFresh owner leftName.value leftType).ids.head? = some ⟨owner, nextIndex⟩ ∧
            (inputs.bindFresh owner rightName.value rightType).ids.head? = some ⟨owner, nextIndex⟩)) "sibling allocation was threaded globally"
      | _, _ => pure ()
      inspect owner inputs thenBody thenCore type nextIndex
      inspect owner inputs elseBody elseCore type nextIndex
  | ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩, _ =>
      have _ := elaborateTypedLetReturnTree?_single types owner inputs returned blockSpan returnSpan
      assertTrue (decide (elaborateReturnBody? inputs.names inputs.context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =
        some (core, type))) "terminal return lost its independent Core or extended variable positions"
  | _, _ => throw (IO.userError "source shape differs from independent ordered Core")
termination_by sizeOf body
private def accepted (content : String) (parameters : List (String × Core.Ty))
    (core : Core.Expr) (type : Core.Ty) (branchBindings : Bool) : IO Unit := do
  let some source ← parsed? content | throw (IO.userError s!"positive declaration did not completely parse: {content}")
  for owner in owners do
    let inputs ← declaredInputs source owner parameters
    assertTrue (decide (interpretRuntimeFunctionHeader? types source.value.signature = some type)) "positive header failed independently"
    match result : elaborateTypedLetReturnTree? types owner inputs source.value.body with
    | none => throw (IO.userError s!"valid recursive tree rejected: {content}")
    | some (actualCore, actualType) =>
        let elaboration := elaborateTypedLetReturnTree?_elaborates result
        let typing := elaborateTypedLetReturnTree?_sound result
        have _ := elaborateTypedLetReturnTree?_iff.mp result
        have _ := elaboration.complete
        have _ := elaboration.hasType
        have _ := typing.elaborates_exact
        have _ := typing.elaborates
        have _ := typing.type_unique typing
        have _ := typedLetReturnTreeHasType_iff_elaborates_exact.mp typing
        have _ := typedLetReturnTreeHasType_iff_elaborates.mp typing
        have _ := elaborateTypedLetReturnTree?_core_hasType result
        assertTrue (decide (actualCore = core ∧ actualType = type ∧ Core.infer? inputs.context.values core = some type))
          "independent tree Core, return type or original free positions changed"
        let wrong := Core.Expr.ifE (.bool true) core core
        if different : wrong ≠ actualCore then
          have _ := excludeWrong elaboration different
          assertTrue (decide (Core.infer? inputs.context.values wrong = some type)) "wrong-source contrast was not equally typed"
        else throw (IO.userError "wrong-source contrast became identical")
        inspect owner inputs source.value.body core type parameters.length
        assertTrue (decide ((compileRuntimeFunction? types owner source).map (fun compiled =>
          (compiled.core, compiled.returnType, compiled.inputs.names, compiled.inputs.context.values)) =
            some (core, type, inputs.names, inputs.context.values))) "entry changed independent Core/type or original parameters"
        if branchBindings then
          assertTrue ((elaborateTypedLetReturnBody? types owner inputs source.value.body).isNone &&
            (elaborateTerminalReturnTree? inputs.names inputs.context source.value.body).isNone) "recursive entry broadened an old body adapter"
        else
          assertTrue (decide (elaborateTypedLetReturnBody? types owner inputs source.value.body = some (core, type) ∧
            (compileRuntimeFunction? types owner source).map (fun compiled => (compiled.core, compiled.returnType)) = some (core, type)))
            "old accepted body or entry changed exact Core/type"
    compatibility owner inputs source.value.body
private def alternating (remaining level : Nat) (annotation : String) : String × Core.Expr :=
  match remaining with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 2 else 0))
  | count + 1 =>
      let (tail, core) := alternating count (level + 1) annotation
      let recursiveText := s!"let z{level}: {annotation}=" ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail
      let leafText := s!"let z{level}: {annotation}=y;return z{level};"
      let recursiveCore := Core.Expr.letE (.var (if level = 0 then 2 else 0)) core
      let leafCore := Core.Expr.letE (.var (level + 1)) (.var 0)
      if level % 2 = 0 then ("if(c){" ++ recursiveText ++ "}else{" ++ leafText ++ "}", .ifE (.var level) recursiveCore leafCore)
      else ("if(c){" ++ leafText ++ "}else{" ++ recursiveText ++ "}", .ifE (.var level) leafCore recursiveCore)
private def rejected (body : String) : IO Unit := do
  let some source ← parsed? ("function rejected(x: Word,y: Word,c: Bool,q: Opaque,f: Fn) returns (Word)" ++ body)
    | throw (IO.userError s!"semantic rejection did not completely parse: {body}")
  for owner in owners do
    let inputs ← declaredInputs source owner [("x", .word), ("y", .word), ("c", .bool), ("q", .namedData ⟨91⟩), ("f", .function .word (.namedData ⟨91⟩))]
    assertTrue (decide (interpretRuntimeFunctionHeader? types source.value.signature = some .word)) "negative body had an invalid header"
    match failed : elaborateTypedLetReturnTree? types owner inputs source.value.body with
    | some _ => throw (IO.userError s!"whole-tree rejection bypassed: {body}")
    | none =>
        have _ := elaborateTypedLetReturnTree?_eq_none_iff.mp failed
        assertTrue (compileRuntimeFunction? types owner source).isNone "rejected tree changed an old entry"
    compatibility owner inputs source.value.body
private def dictionaryBoundary : IO Unit := do
  let some source ← parsed? "function meaning(x: Opaque,c: Bool) returns (Opaque){if(c){let z: Alias=x;return z;}else{let z: Opaque=x;return z;}}"
    | throw (IO.userError "type-meaning contrast did not parse")
  for owner in owners do
    let inputs ← declaredInputs source owner [("x", .namedData ⟨91⟩), ("c", .bool)]
    let expected : Option (Core.Expr × Core.Ty) := some (.ifE (.var 0) (.letE (.var 1) (.var 0)) (.letE (.var 1) (.var 0)), .namedData ⟨91⟩)
    assertTrue (decide (elaborateTypedLetReturnTree? types owner inputs source.value.body = expected ∧
      elaborateTypedLetReturnTree? (types ++ [(["Alias"], .word)]) owner inputs source.value.body = expected ∧
      elaborateTypedLetReturnTree? ((["Alias"], .word) :: types) owner inputs source.value.body = none ∧
      types.lookup? ["Pkg", "Token"] = some (.namedData ⟨92⟩) ∧ types.lookup? ["Pkg.Token"] = some .word))
      "fixed inputs ignored first-match branch annotation meanings or flattened qualified keys"

def frontendParsedTypedLetReturnTreeTests : IO Unit := do
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for (annotation, type) in [("Word", Core.Ty.word), ("Bool", .bool), ("Unit", .unit), ("Cell", .cell .word),
      ("Fn", .function .word (.namedData ⟨91⟩)), ("Opaque", .namedData ⟨91⟩), ("Pkg.Token", .namedData ⟨92⟩)] do
    for depth in [0, 1, 2, 5, 16, 40] do
      let (body, core) := alternating depth 0 annotation
      accepted (s!"function alternating(x: {annotation},y: {annotation},c: Bool) returns ({annotation})" ++ "{" ++ body ++ "}")
        [("x", type), ("y", type), ("c", .bool)] core type (depth != 0)
  accepted "function ordered(x: Word,y: Word,c: Bool) returns (Word){let a: Word=x;if(c){let b: Word=a - y;return b;}else{let b: Word=y - a;return b;}}"
    [("x", .word), ("y", .word), ("c", .bool)] (.letE (.var 2) (.ifE (.var 1)
      (.letE (.binary .wordSub (.var 0) (.var 2)) (.var 0)) (.letE (.binary .wordSub (.var 2) (.var 0)) (.var 0)))) .word true
  for count in [1, 3, 20] do
    let indices := List.range count
    let prefixText := String.join (indices.map fun index => s!"let a{index}: Word=" ++ (if index = 0 then "x" else s!"a{index - 1}") ++ ";")
    let left := indices.foldr (fun index tail => Core.Expr.letE (.var (if index = 0 then 1 else 0)) tail) (.var 0)
    accepted ("function longArm(x: Word,c: Bool) returns (Word){if(c){" ++ prefixText ++ s!"return a{count - 1};" ++ "}else{return x;}}")
      [("x", .word), ("c", .bool)] (.ifE (.var 0) left (.var 1)) .word true
  accepted "function bare(c: Bool,q: Opaque){if(c){let z: Alias=q;return;}else{let z: Opaque=q;return;}}"
    [("c", .bool), ("q", .namedData ⟨91⟩)] (.ifE (.var 1) (.letE (.var 0) .unit) (.letE (.var 0) .unit)) .unit true
  accepted "function differentSiblingTypes(x: Word,c: Bool){if(c){let z: Word=x;return;}else{let z: Bool=c;return;}}"
    [("x", .word), ("c", .bool)] (.ifE (.var 0) (.letE (.var 1) .unit) (.letE (.var 0) .unit)) .unit true
  accepted "function qualified(x: Pkg.Token,c: Bool) returns (Pkg.Token){if(c){let z: Pkg /* components */ . Token=x;return z;}else{return x;}}"
    [("x", .namedData ⟨92⟩), ("c", .bool)] (.ifE (.var 0) (.letE (.var 1) (.var 0)) (.var 1)) (.namedData ⟨92⟩) true
  accepted "function old(c: Bool,x: Word) returns (Word){if(c){if(c){return x;}else{return x;}}else{return x;}}"
    [("c", .bool), ("x", .word)] (.ifE (.var 1) (.ifE (.var 1) (.var 0) (.var 0)) (.var 0)) .word false
  accepted "function prefix(x: Word,c: Bool) returns (Word){let z: Word=x;if(c){return z;}else{return x;}}"
    [("x", .word), ("c", .bool)] (.letE (.var 1) (.ifE (.var 1) (.var 0) (.var 2))) .word false
  accepted "function bare(){return;}" [] .unit .unit false
  dictionaryBoundary
  accepted "function rejected(x: Word,y: Word,c: Bool,q: Opaque,f: Fn) returns (Word){if(c){let z=x;return z;}else{return y;}}"
    [("x", .word), ("y", .word), ("c", .bool), ("q", .namedData ⟨91⟩), ("f", .function .word (.namedData ⟨91⟩))]
    (.ifE (.var 2) (.letE (.var 4) (.var 0)) (.var 3)) .word true
  for body in ["{if(c){let z: Word;return x;}else{return y;}}",
      "{if(c){let z;return x;}else{return y;}}", "{if(c){let z: Word=z;return x;}else{return y;}}",
      "{if(c){let a: Word=b;let b: Word=x;return a;}else{return y;}}",
      "{if(c){let z: Word=x;return z;}else{return z;}}", "{if(c){return z;}else{let z: Word=y;return z;}}",
      "{if(c){let z: Word=x;return z;}else{let a: Word=z;return a;}}", "{if(c){let x: Word=y;return x;}else{return y;}}",
      "{let a: Word=x;if(c){let a: Word=y;return a;}else{return y;}}",
      "{if(c){let z: Word=x;let z: Word=y;return z;}else{return y;}}",
      "{if(c){return x;}else{let z: Word=missing;return y;}}", "{if(c){return x;}else{let z: Unknown=y;return y;}}",
      "{if(c){return x;}else{let z: Bool=y;return y;}}", "{if(c){return x;}else{let z: Word<Bool> =y;return y;}}",
      "{if(c){let z: Word=c ? x : missing;return x;}else{return y;}}",
      "{if(c){let z: Word=x;return z;}else{let z: Bool=c;return z;}}", "{if(x){let z: Word=x;return z;}else{return y;}}",
      "{if(c){let z: Word=x;if(z){return z;}else{return y;}}else{return y;}}",
      "{if(c){let z: Word=x;return z;}}", "{if(c){let z: Word=x;return z;}else{return y;}return x;}",
      "{if(c){{let z: Word=x;return z;}}else{return y;}}", "{if(c){let z: Word=x;z=y;return z;}else{return y;}}",
      "{if(c){let z: Word=x;return z;return y;}else{return y;}}", "{if(c){let z: Word=x;}else{return y;}}",
      "{if(c){return x;}else{let z: Opaque=f(x);return y;}}",
      "{if(0 == 0){return x;}else{let a: Word=y;if(c){let b: Word=a;return b;}else{let b: Word=missing;return a;}}}",
      "{return missing;}", "{}"] do rejected body
  rejected ("{if(0 == 0){return x;}else{let z: Word=" ++ toString (2 ^ 256 : Nat) ++ ";return y;}}")
  for content in ["function incomplete(x: Word){if(0 == 0){let z: Word=;return z;}else{return x;}}",
      "function missing(x){return x;}", "function incomplete(){return;", "function trailing(){return;} trailing"] do
    assertTrue (← parsed? content).isNone "incomplete source acquired static meaning"

end Tests
