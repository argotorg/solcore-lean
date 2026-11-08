import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.Fragments.Internal.TypedLet
import Solcore.Frontend.Fragments.Internal.RuntimeFunctions
import Solcore.Frontend.Fragments.Internal.LocalFunctionApplication
import Solcore.Frontend.Fragments.Internal.ReturnBodies
import Solcore.Core.Safety

/-!
# Typed let body tests

Typed let return bodies: evaluation, owners, type extension and runtime entries.
-/

section
-- leanmerge: from Solcore.Test.FrontendParsedTypedLetReturnBodies
/-! Parsed typed prefixes retain original initializer scopes and exact ordered
Core without argument values. Recursive entries include this older adapter;
the old body boundaries remain narrower, including for nominal inputs. -/

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

private def rejected (body : String) (entryCore : Option Core.Expr := none) : IO Unit := do
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
        match entryCore with
        | none => assertTrue (compileRuntimeFunction? types owner source).isNone "invalid whole body entered runtime compilation"
        | some core => assertTrue (decide (Core.infer? inputs.context.values core = some .word ∧
            (compileRuntimeFunction? types owner source).map (fun compiled =>
              (compiled.core, compiled.returnType, compiled.inputs.names, compiled.inputs.context.values)) =
                some (core, .word, inputs.names, inputs.context.values))) "recursive entry changed exact Core or original parameter-only rows"
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
  for (body, core) in [("{let z = x;return z;}", Core.Expr.letE (.var 4) (.var 0)),
      ("{let z: Word = x;{return z;}}", .letE (.var 4) (.var 0)),
      ("{let z: Word = x;if(c){let a: Word = z;return a;}else{return z;}}",
        Core.Expr.letE (.var 4) (.ifE (.var 3) (.letE (.var 0) (.var 0)) (.var 0))),
      ("{let z: Word = x;if(0 == 0){return z;}else{let a: Word = z;return a;}}",
        .letE (.var 4) (.ifE (.binary .wordEq (.word Core.Word.zero) (.word Core.Word.zero)) (.var 0) (.letE (.var 0) (.var 0)))),
      ("{if(c){let z: Word = x;return z;}else{return y;}}", .ifE (.var 2) (.letE (.var 4) (.var 0)) (.var 3))] do
    rejected body (some core)
  rejected ("{let z: Word = " ++ toString (2 ^ 256 : Nat) ++ ";return x;}")
  for body in ["{let z: Word;return x;}", "{let z;return x;}",
      "{let z: Word = z;return x;}", "{let a: Word = b;let b: Word = x;return a;}",
      "{let x: Word = y;return x;}", "{let z: Word = x;let z: Word = y;return z;}",
      "{let z: Word = missing;return x;}", "{let z: Bool = x;return x;}",
      "{let z: Unknown = x;return x;}", "{let z: Word<Bool> = x;return x;}",
      "{let z: Pkg.Token = x;return x;}", "{let z: Opaque = c;return x;}",
      "{let z: Opaque = f(x);return x;}", "{let z: Word = (0 == 0) ? x : missing;return x;}",
      "{let z: Word = x;}", "{let z: Word = x;return z;return x;}",
      "{let z: Word = x;z = y;return z;}",
      "{let z: Word = x;if(c){return z;}}", "{let z: Word = x;if(x){return z;}else{return y;}}",
      "{let z: Word = x;if(0 == 0){return z;}else{if(c){return y;}else{return missing;}}}",
      "{let z: Word = x;if(0 == 0){return z;}else{return c;}}",
      "{return missing;}", "{if(0 == 0){return x;}else{return missing;}}"] do rejected body
  for content in ["{let z: Word = ;return z;}", "{let z: Word = x return z;}",
      "{let z: Word = x;return z;", "{let z: Word = x;return z;} trailing"] do
    assertTrue (← parsed? (Syntax.Parser.block .allow) content).isNone "incomplete binding acquired static meaning"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTypedLetReturnBodyEvaluation
/-! Actual parsed initializers certify their old-scope values before adding
bindings. Fixture scripts construct source paths, never derive expectations
from Core execution, and distinguish raw success from whole acceptance. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"PrefixEvaluation", by decide⟩], by decide⟩⟩, 9⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def types_variant : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def stores : List Core.Store := [[.word (word 101), .cellRef .word 31],
  [.closure .bool .bool (.var 0) [], .bool false, .word Core.Word.maximum]]
private def actual (content : String) (arguments : List TypedRuntimeArgument) : IO (Syntax.FunctionDecl × LocalInputs) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-prefix-evaluation.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "function did not completely parse")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "function was diagnosed or incompletely consumed"
  match bound : bindRuntimeParameters? types_variant owner source.value.signature.parameters.elements arguments with
  | none => throw (IO.userError "actual typed arguments did not bind")
  | some inputs =>
      have declared := (bindRuntimeParameters?_sound bound).erase_values
      have _ := declared.complete
      assertTrue (decide (inputs.environment.values = (arguments.map (·.value)).reverse ∧
        (declareRuntimeParameters? types_variant owner source.value.signature.parameters.elements).map (fun i => (i.names, i.context)) =
          some (inputs.names, inputs.context))) "actual values were reordered or static factorization changed"
      return (source, inputs)

private structure ExprCertificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table environment store source value store cost
private def reference (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (ExprCertificate table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "script expected an existing source name")
      | some id =>
          match found : environment.lookup? id with
          | none => throw (IO.userError "script expected an existing actual value")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | _ => throw (IO.userError "script expected an actual reference")
private def expression (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (ExprCertificate table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier _⟩ => reference table environment store source
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let child ← reference table environment store operand
      match valueAt : child.value with
      | .word value => return ⟨.word value.bitNot, child.cost + 2, by rw [sourceAt]; exact .bitNot (by simpa only [valueAt] using child.costed)⟩
      | _ => throw (IO.userError "bit-not script expected Word")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let first ← reference table environment store left
      let second ← reference table environment store right
      match leftAt : first.value, rightAt : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), first.cost + second.cost + 3, by
          rw [sourceAt]
          exact .subtract (by simpa only [leftAt] using first.costed) (by simpa only [rightAt] using second.costed)⟩
      | _, _ => throw (IO.userError "ordered subtraction script expected Words")
  | ⟨_, .conditional condition _ left _ _⟩ =>
      let guard ← reference table environment store condition
      let selected ← reference table environment store left
      if agrees : guard.value = .bool true then
        return ⟨selected.value, guard.cost + selected.cost + 2, by rw [sourceAt]; exact .ifTrue (agrees ▸ guard.costed) selected.costed⟩
      else throw (IO.userError "initializer script requires the supplied true branch")
  | _ => throw (IO.userError "initializer is outside the fixture script")

private structure TreeCertificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TerminalReturnTreeEvaluatesWithCost table environment store source value store cost
private def tree (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) (choices : List Bool) : IO (TreeCertificate table environment store source) := do
  match choices, sourceAt : source with
  | [], ⟨_, [⟨_, .returnStmt none⟩]⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | [], ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      let child ← expression table environment store operand
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .single (.expression child.costed)⟩
  | choice :: rest, ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩ =>
      let guard ← reference table environment store condition
      if agrees : guard.value = .bool choice then
        match choiceAt : choice with
        | true =>
            let child ← tree table environment store left rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [sourceAt]
              exact .ifTrue (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
        | false =>
            let child ← tree table environment store right rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [sourceAt]
              exact .ifFalse (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
      else throw (IO.userError "branch script disagrees with the actual guard")
  | _, _ => throw (IO.userError "branch script does not describe the original terminal tree")
termination_by choices.length

private structure Certificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  raw : TypedLetReturnBodyEvaluates owner table environment store source value store
  costed : TypedLetReturnBodyEvaluatesWithCost owner table environment store source value store cost
private def certify (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) (choices : List Bool) : IO (Certificate table environment store source) := do
  match sourceAt : source with
  | ⟨blockSpan, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let child ← expression table environment store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let tail ← certify ((name.value, id) :: table) ((id, child.value) :: environment) store ⟨blockSpan, rest⟩ choices
      return ⟨tail.value, child.cost + tail.cost + 2, by rw [sourceAt]; exact .binding child.costed.erase tail.raw,
        by rw [sourceAt]; exact .binding child.costed tail.costed⟩
  | _ =>
      let child ← tree table environment store source choices
      have _ := child.costed.erase.typedLetReturnBody owner
      have _ := child.costed.typedLetReturnBody owner
      return ⟨child.value, child.cost, .terminal child.costed.erase, .terminal child.costed⟩
termination_by source.value.length

private theorem arbitraryContinuation {inputs : LocalTypeInputs} {environment : Resolved.Environment}
    {store : Core.Store} {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (certificate : Certificate inputs.names environment store source)
    (accepted : elaborateTypedLetReturnBody? types_variant owner inputs source = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) (continuation : List Core.Frame) :
    Core.Steps certificate.cost ⟨.eval core environment.values, continuation, store⟩
      ⟨.ret certificate.value, continuation, store⟩ :=
  certificate.costed.checked_toStepsWithContinuation accepted sameIds continuation

private def checked (source : Syntax.FunctionDecl) (inputs : LocalInputs) (choices : List Bool)
    (expected : Core.Expr) (value : Core.Value) (cost : Nat) : IO Unit := do
  let arguments := inputs.bindings.reverse.map (fun row => (⟨row.type, row.value, row.valueTyped⟩ : TypedRuntimeArgument))
  have sameIds : inputs.environment.ids = inputs.toTypeInputs.context.ids := by
    simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
  have typedEnvironment : Core.EnvironmentHasTypes inputs.environment.values inputs.toTypeInputs.context.values := by
    simpa only [LocalInputs.toTypeInputs_context] using inputs.environmentTyped
  have _ := inputs.toTypeInputs.names_ids
  for store in stores do
    let certificate ← certify inputs.toTypeInputs.names inputs.environment store source.value.body choices
    assertTrue (decide (certificate.value = value ∧ certificate.cost = cost)) "independent source value or cost changed"
    match accepted : elaborateTypedLetReturnBody? types_variant owner inputs.toTypeInputs source.value.body with
    | none => throw (IO.userError "whole prefix checking failed")
    | some (core, type) =>
        let typing := elaborateTypedLetReturnBody?_sound accepted
        assertTrue (decide (interpretRuntimeFunctionHeader? types_variant source.value.signature = some type)) "entry header disagreed with the checked return type"
        have _ := typing.evaluates sameIds typedEnvironment store
        have _ := certificate.raw.preserves_type typing sameIds typedEnvironment
        have _ := certificate.raw.store_eq
        have _ := certificate.raw.exists_cost
        have _ := typedLetReturnBodyEvaluates_iff_exists_cost.mp certificate.raw
        have _ := certificate.raw.deterministic certificate.costed.erase
        have _ := certificate.costed.store_eq
        have _ := certificate.costed.cost_pos
        have _ := certificate.costed.deterministic certificate.costed
        let bridge := elaborateTypedLetReturnBody?_evaluates_iff accepted sameIds
        have _ := bridge.mpr (bridge.mp certificate.raw)
        have _ := certificate.costed.checked_toSteps accepted sameIds
        have _ := arbitraryContinuation certificate accepted sameIds
        assertTrue (decide (core = expected ∧ Core.infer? inputs.context.values core = some type ∧
          Core.runStateful cost (.initial core inputs.environment.values store) = .done value store)) "actual accepted Core lost the certified endpoint"
        assertTrue (decide ((compileRuntimeFunction? types_variant owner source).map (fun compiled =>
          (compiled.core, compiled.returnType, compiled.inputs.names, compiled.inputs.context.values)) = some (expected, type, inputs.names, inputs.context.values) ∧
          runRuntimeFunction? types_variant owner source arguments cost store = some (type, .done value store))) "integrated entry changed original parameters, Core or certified execution"
        let safe : List Core.Frame := [.letBody (.var 0) [.word (word 17)], .unaryApply .wordNot]
        have _ := arbitraryContinuation certificate accepted sameIds safe
        assertTrue (decide (Core.runStateful cost ⟨.eval core inputs.environment.values, safe, store⟩ =
          .outOfFuel ⟨.ret value, safe, store⟩)) "retained continuation was changed or executed"
        if (Core.UnaryOp.wordNot.apply value).isNone then
          let bad : List Core.Frame := [.unaryApply .wordNot]
          have _ := arbitraryContinuation certificate accepted sameIds bad
          assertTrue (decide (Core.runStateful cost ⟨.eval core inputs.environment.values, bad, store⟩ =
            .fault (.invalidUnaryOperand .wordNot value) ⟨.ret value, bad, store⟩)) "zero remaining fuel concealed an incompatible continuation"

private theorem initializerRequired {table : LocalNameTable} {environment : Resolved.Environment}
    {store : Core.Store} {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
    (absent : ¬ ∃ value finalStore, LocalExpressionEvaluates table environment store initializer value finalStore) :
    ¬ ∃ value finalStore, TypedLetReturnBodyEvaluates owner table environment store
      ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ value finalStore := by
  rintro ⟨value, finalStore, evaluation⟩
  cases evaluation with
  | terminal child => cases child with | single returned => cases returned
  | binding child _ => exact absent ⟨_, _, child⟩

private def boundaries : IO Unit := do
  let args : List TypedRuntimeArgument := [⟨.word, .word (word 9), .word⟩, ⟨.word, .word (word 2), .word⟩]
  let (missing, initial) ← actual "function missing(x: Word,r: Word) returns (Word){let z: Word=missing;return x;}" args
  for store in stores do
    match missing.value.body with
    | ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some ⟨span, .identifier referenceName⟩)⟩ :: rest⟩ =>
        if absent : initial.names.lookup? referenceName.value = none then
          have impossible : ¬ ∃ value finalStore, LocalExpressionEvaluates initial.names initial.environment store
              ⟨span, .identifier referenceName⟩ value finalStore := by
            rintro ⟨value, finalStore, evaluated⟩
            cases evaluated with
            | identifier named _ =>
                have found := LocalNameTable.lookup?_iff.mpr named
                rw [absent] at found
                cases found
          have _ := initializerRequired (blockSpan := blockSpan) (letSpan := letSpan)
            (name := name) (annotation := annotation) (rest := rest) impossible
          assertTrue (elaborateTypedLetReturnBody? types_variant owner initial.toTypeInputs missing.value.body).isNone
            "unused missing initializer bypassed whole checking"
        else throw (IO.userError "missing initializer name was unexpectedly bound")
    | _ => throw (IO.userError "strictness fixture lost its actual let/reference syntax")
  let (source, inputs) ← actual "function alignment(x: Word,r: Word) returns (Word){let z: Word=x;return z;}" args
  let untyped : Resolved.Environment := inputs.environment.map fun entry => (entry.1, Core.Value.bool true)
  have aligned : untyped.ids = inputs.toTypeInputs.context.ids := by
    simpa only [untyped, Resolved.LocalScope.ids, List.map_map, Function.comp_def, LocalInputs.toTypeInputs_context] using inputs.sameIds
  for store in stores do
    let certificate ← certify inputs.toTypeInputs.names untyped store source.value.body []
    match accepted : elaborateTypedLetReturnBody? types_variant owner inputs.toTypeInputs source.value.body with
    | none => throw (IO.userError "aligned untyped contrast lost static acceptance")
    | some (core, type) =>
        let bridge := elaborateTypedLetReturnBody?_evaluates_iff accepted aligned
        have _ := bridge.mpr (bridge.mp certificate.raw)
        have _ := certificate.costed.checked_toSteps accepted aligned
        have _ := arbitraryContinuation certificate accepted aligned
        assertTrue (decide (core = .letE (.var 1) (.var 0) ∧ type = .word ∧ certificate.value = .bool true ∧ certificate.cost = 4 ∧
          Core.runStateful 4 (.initial core untyped.values store) = .done (.bool true) store)) "aligned raw bridge inferred runtime typing"
        let reordered : Resolved.Environment := inputs.environment.reverse
        let raw ← certify inputs.names reordered store source.value.body []
        assertTrue (decide (reordered.ids ≠ inputs.context.ids ∧ raw.value = .word (word 9) ∧ raw.cost = 4 ∧
          Core.runStateful 4 (.initial core reordered.values store) = .done (.word (word 2)) store)) "misaligned identities preserved positional meaning"

def frontendParsedTypedLetReturnBodyEvaluationTests : IO Unit := do
  boundaries
  for count in [1, 2, 5, 12] do
    let indices := List.range count
    let declarations := String.join (indices.map fun index => "let z" ++ toString index ++ ": Word=" ++
      (if index = 0 then "x" else s!"z{index - 1}") ++ ";")
    let (source, inputs) ← actual ("function chain(x: Word) returns (Word){" ++ declarations ++ s!"return z{count - 1};" ++ "}")
      [⟨.word, .word (word 9), .word⟩]
    checked source inputs [] (indices.foldr (fun _ tail => Core.Expr.letE (.var 0) tail) (.var 0)) (.word (word 9)) (3 * count + 1)
  for (x, r) in [(word 9, word 2), (Core.Word.zero, Core.Word.maximum), (word (2 ^ 255), word 7)] do
    let args : List TypedRuntimeArgument := [⟨.word, .word x, .word⟩, ⟨.word, .word r, .word⟩]
    for (text, core, value, cost) in [
        ("{let y: Word=x;let z: Word=y - x;return z;}", Core.Expr.letE (.var 1)
          (.letE (.binary .wordSub (.var 0) (.var 2)) (.var 0)), Core.Value.word Core.Word.zero, 11),
        ("{let y: Word=x;let z: Word=y - r;return z;}", .letE (.var 1)
          (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0)), .word (x.sub r), 11),
        ("{let z: Word=x - r;return x;}", .letE (.binary .wordSub (.var 1) (.var 0)) (.var 2), .word x, 8)] do
      let (source, inputs) ← actual ("function ordered(x: Word,r: Word) returns (Word)" ++ text) args
      checked source inputs [] core value cost
    for c in [false, true] do
      for d in [false, true] do
        let (source, inputs) ← actual "function asymmetric(c: Bool,d: Bool,x: Word,r: Word) returns (Word){let y: Word=x;if(c){if(d){return ~y;}else{return y - r;}}else{return r;}}"
          ([⟨.bool, .bool c, .bool⟩, ⟨.bool, .bool d, .bool⟩] ++ args)
        checked source inputs (if c then [true, d] else [false]) (.letE (.var 1)
          (.ifE (.var 4) (.ifE (.var 3) (.unary .wordNot (.var 0)) (.binary .wordSub (.var 0) (.var 1))) (.var 1)))
          (.word (if c then if d then x.bitNot else x.sub r else r)) (if c then if d then 12 else 14 else 7)
  let pool : List (String × TypedRuntimeArgument) := [("Cell", ⟨.cell .word, .cellRef .word 29, .cellRef⟩),
    ("Fn", ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩),
    ("Unit", ⟨.unit, .unit, .unit⟩)]
  for (name, argument) in pool do
    let (source, inputs) ← actual (s!"function opaque(x: {name}) returns ({name})" ++ "{let z: " ++ name ++ "=x;return z;}") [argument]
    checked source inputs [] (.letE (.var 0) (.var 0)) argument.value 4
    let (bare, bareInputs) ← actual (s!"function bare(x: {name})" ++ "{let z: " ++ name ++ "=x;return;}") [argument]
    checked bare bareInputs [] (.letE (.var 0) .unit) .unit 4
  let args : List TypedRuntimeArgument := [⟨.word, .word (word 9), .word⟩, ⟨.word, .word (word 2), .word⟩, ⟨.bool, .bool true, .bool⟩]
  for (bodyText, choices, value, cost) in [
      ("{let z: Word=c ? x : missing;return x;}", [], Core.Value.word (word 9), 7),
      ("{let z: Unknown=x;return z;}", [], .word (word 9), 4),
      ("{let z: Bool=x;return z;}", [], .word (word 9), 4),
      ("{let x: Word=r;return x;}", [], .word (word 2), 4),
      ("{let z: Word=x;if(c){if(c){return z;}else{return missing;}}else{return r;}}", [true, true], .word (word 9), 10),
      ("{let z: Word=x;if(c){return z;}else{return c;}}", [true], .word (word 9), 7)] do
    let (source, inputs) ← actual ("function raw(x: Word,r: Word,c: Bool) returns (Word)" ++ bodyText) args
    for store in stores do
      let certificate ← certify inputs.names inputs.environment store source.value.body choices
      have _ := certificate.raw.store_eq
      have _ := certificate.raw.exists_cost
      have _ := certificate.costed.cost_pos
      assertTrue (decide (certificate.value = value ∧ certificate.cost = cost) &&
        (elaborateTypedLetReturnBody? types_variant owner inputs.toTypeInputs source.value.body).isNone) "raw selected path was mistaken for whole acceptance"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTypedLetReturnBodyOwners
/-! Owner-only allocation changes actual IDs, not the parsed source, original
scope positions or full fixed-store checkpoints. Nominal cases remain value-free. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def owner_variant : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"PrefixOwners", by decide⟩], by decide⟩⟩, 17⟩
private def shift (id : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { id with declarationIndex := id.declarationIndex + 11 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  change left.declarationIndex + 11 = right.declarationIndex + 11 at indices
  have original := Nat.add_right_cancel indices
  cases left; cases right; simp_all [shift]
private theorem shiftNotSurjective : ¬ Function.Surjective shift := by
  intro surjective
  obtain ⟨original, same⟩ := surjective { owner_variant with declarationIndex := 0 }
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  change original.declarationIndex + 11 = 0 at indices
  omega
private def mapping := ownerLocalIdMap shift
private theorem mappingInjective : Function.Injective mapping := ownerLocalIdMap_injective shift shiftInjective
private def types_variant2 : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
  (["Alias"], .namedData ⟨91⟩), (["Pkg", "Token"], .namedData ⟨92⟩),
  (["FnOpaque"], .function .word (.namedData ⟨91⟩)), (["Opaque"], .bool)]
private def stores_variant : List Core.Store := [[.word (word 91), .cellRef .word 40],
  [.closure .bool .bool (.var 0) [], .bool true, .word Core.Word.maximum]]
private def parsed {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO α := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-prefix-owners.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := parser (Syntax.Parser.State.initial file lexed) | throw (IO.userError s!"fixture did not parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "incomplete or diagnosed source"
  return source
private def declared (source : Syntax.FunctionDecl) : IO LocalTypeInputs := do
  let parameters := source.value.signature.parameters.elements
  match accepted : declareRuntimeParameters? types_variant2 owner_variant parameters with
  | none => throw (IO.userError "value-free source parameters did not declare")
  | some inputs =>
      have _ := declareRuntimeParameters?_sound accepted
      let rows := parameters.filterMap fun parameter => match parameter.value with
        | .typed none name annotation => (interpretTypeName? types_variant2 annotation).map (name.value, ·)
        | _ => none
      assertTrue (decide (rows.length = parameters.length ∧ inputs.names.map Prod.fst = (rows.map Prod.fst).reverse ∧
        inputs.context.values = (rows.map Prod.snd).reverse ∧ inputs.ids =
          (List.range parameters.length).reverse.map (fun index => (⟨owner_variant, index⟩ : Resolved.LocalId)))) "declaration changed original source rows"
      return inputs

private def relabeled (inputs : LocalTypeInputs) (body : Syntax.Block) : IO LocalTypeInputs := do
  let mapped := inputs.mapIds mapping mappingInjective
  have _ := elaborateTypedLetReturnBody?_mapOwner shift shiftInjective types_variant2 owner_variant inputs body
  assertTrue (decide (mapped.ids = inputs.ids.map mapping ∧ mapped.ids.map (·.binderIndex) = inputs.ids.map (·.binderIndex) ∧
    mapped.names.map Prod.fst = inputs.names.map Prod.fst ∧ mapped.context.values = inputs.context.values ∧
    elaborateTypedLetReturnBody? types_variant2 (shift owner_variant) mapped body = elaborateTypedLetReturnBody? types_variant2 owner_variant inputs body))
    "owner relabeling changed names, index positions, type rows or complete optional checking"
  if !inputs.bindings.isEmpty then assertTrue (decide (mapped.ids ≠ inputs.ids)) "nontrivial owner shift left IDs unchanged"
  match checked : elaborateTypedLetReturnBody? types_variant2 owner_variant inputs body with
  | none => pure ()
  | some _ =>
      have _ := (elaborateTypedLetReturnBody?_elaborates checked).mapOwner shift shiftInjective
      have _ := (elaborateTypedLetReturnBody?_sound checked).mapOwner shift shiftInjective
      pure ()
  return mapped
private def inspect (inputs : LocalTypeInputs) (body : Syntax.Block) (core : Core.Expr)
    (type : Core.Ty) (nextIndex : Nat) : IO Unit := do
  match body, core with
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩, .letE initial tail =>
      let some boundType := interpretTypeName? types_variant2 annotation | throw (IO.userError "lost annotation meaning")
      let mapped := inputs.mapIds mapping mappingInjective
      let extended := inputs.bindFresh owner_variant name.value boundType
      let extendedMapped := mapped.bindFresh (shift owner_variant) name.value boundType
      have _ := Resolved.freshLocalId_map_owner shift shiftInjective owner_variant inputs.ids
      have _ := inputs.bindFresh_mapOwner owner_variant shift shiftInjective name.value boundType
      assertTrue (decide (Resolved.freshLocalId owner_variant inputs.ids = ⟨owner_variant, nextIndex⟩ ∧
        Resolved.freshLocalId (shift owner_variant) mapped.ids = ⟨shift owner_variant, nextIndex⟩ ∧
        extendedMapped.ids = extended.ids.map mapping ∧ extendedMapped.context.values = extended.context.values ∧
        extendedMapped.names.map Prod.fst = extended.names.map Prod.fst ∧
        elaborateLocalExpression? inputs.names inputs.context initializer = some (initial, boundType) ∧
        elaborateLocalExpression? mapped.names mapped.context initializer = some (initial, boundType) ∧
        elaborateTypedLetReturnBody? types_variant2 owner_variant extended ⟨blockSpan, rest⟩ = some (tail, type) ∧
        elaborateTypedLetReturnBody? types_variant2 (shift owner_variant) extendedMapped ⟨blockSpan, rest⟩ = some (tail, type)))
        "fresh identity, original initializer scope or extended tail order changed"
      inspect extended ⟨blockSpan, rest⟩ tail type (nextIndex + 1)
  | _, _ =>
      assertTrue (decide (elaborateTerminalReturnTree? inputs.names inputs.context body = some (core, type)))
        "independent ordered Core did not end in the actual terminal tree"
termination_by body.value.length
private def checkedStatic (inputs : LocalTypeInputs) (body : Syntax.Block) (core : Core.Expr)
    (type : Core.Ty) (bound nextIndex : Nat) : IO Unit := do
  let mapped ← relabeled inputs body
  assertTrue (decide (elaborateTypedLetReturnBody? types_variant2 owner_variant inputs body = some (core, type) ∧
    elaborateTypedLetReturnBody? types_variant2 (shift owner_variant) mapped body = some (core, type) ∧
    Core.infer? inputs.context.values core = some type ∧ typedLetReturnBodyFuelBound body = bound))
    "independent Core, type or source-only bound changed"
  inspect inputs body core type nextIndex

private def runChecked (inputs : LocalInputs) (body : Syntax.Block) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound nextIndex : Nat) : IO Unit := do
  checkedStatic inputs.toTypeInputs body core type bound nextIndex
  let mapped := inputs.mapIds mapping mappingInjective
  have _ := inputs.checkTypedLetReturnBody?_mapOwner shift shiftInjective types_variant2 owner_variant body
  assertTrue (decide (mapped.ids = inputs.ids.map mapping ∧ mapped.environment.values = inputs.environment.values ∧
    mapped.context.values = inputs.context.values ∧ mapped.names.map Prod.fst = inputs.names.map Prod.fst ∧
    mapped.checkTypedLetReturnBody? types_variant2 (shift owner_variant) body = some (core, type))) "actual values or checked Core changed"
  for store in stores_variant do
    let run := fun fuel => inputs.runTypedLetReturnBody? types_variant2 owner_variant fuel body store
    let shiftedRun := fun fuel => mapped.runTypedLetReturnBody? types_variant2 (shift owner_variant) fuel body store
    match core with
    | .letE initializer tail =>
        let expected : Core.State := ⟨.eval initializer inputs.environment.values, [.letBody tail inputs.environment.values], store⟩
        assertTrue (decide (run 1 = some (type, .outOfFuel expected) ∧ shiftedRun 1 = some (type, .outOfFuel expected)))
          "initial pending let frame did not retain the original actual values"
    | _ => pure ()
    for fuel in List.range (bound + 3) do
      have _ := inputs.runTypedLetReturnBody?_mapOwner shift shiftInjective types_variant2 owner_variant fuel body store
      assertTrue (decide (shiftedRun fuel = run fuel ∧
        run fuel = some (type, Core.runStateful fuel (.initial core inputs.environment.values store))))
        "owner covariance lost a complete same-fuel result"
      if cost ≤ fuel then
        assertTrue (decide (run fuel = some (type, .done value store))) "independent completion value or cost changed"
      else
        match original : run fuel, renamed : shiftedRun fuel with
        | some (originalType, .outOfFuel checkpoint), some (mappedType, .outOfFuel mappedCheckpoint) =>
            assertTrue (decide (originalType = type ∧ mappedType = type ∧ checkpoint = mappedCheckpoint ∧ checkpoint.store = store))
              "owner shift changed a genuine full checkpoint"
            for remaining in List.range (cost - fuel + 3) do
              have _ := LocalInputs.runTypedLetReturnBody?_resume original remaining
              have _ := LocalInputs.runTypedLetReturnBody?_resume renamed remaining
              assertTrue (decide (run (fuel + remaining) = some (type, Core.runStateful remaining checkpoint) ∧
                shiftedRun (fuel + remaining) = some (type, Core.runStateful remaining mappedCheckpoint) ∧
                Core.runStateful remaining checkpoint = Core.runStateful remaining mappedCheckpoint)) "genuine resumption rebuilt or changed a frame"
            assertTrue (decide (Core.runStateful (cost - fuel) checkpoint = .done value store)) "actual residual did not reach the independent expected value"
        | _, _ => throw (IO.userError "below-cost actual checkpoint disappeared")
private def actual_variant (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO LocalInputs := do
  let static ← declared source
  match accepted : bindRuntimeParameters? types_variant2 owner_variant source.value.signature.parameters.elements arguments with
  | none => throw (IO.userError "actual arguments did not bind")
  | some inputs =>
      have _ := (bindRuntimeParameters?_sound accepted).erase_values.complete
      assertTrue (decide (inputs.environment.values = (arguments.map (·.value)).reverse ∧
        inputs.names = static.names ∧ inputs.context = static.context)) "actual argument order disagreed with value-free declaration"
      return inputs
private def fixture (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let source ← parsed (Syntax.Parser.functionDecl .module) content
  let inputs ← actual_variant source arguments
  assertTrue (decide (interpretRuntimeFunctionHeader? types_variant2 source.value.signature = some type)) "body contrast used an invalid header"
  runChecked inputs source.value.body core type value cost bound arguments.length
  for (selectedOwner, expectedIds) in [(owner_variant, inputs.ids), (shift owner_variant, inputs.ids.map mapping)] do
    assertTrue (decide ((compileRuntimeFunction? types_variant2 selectedOwner source).map (fun compiled =>
      (compiled.core, compiled.returnType, compiled.inputs.ids, compiled.inputs.context.values, compiled.inputs.names.map Prod.fst)) =
        some (core, type, expectedIds, inputs.context.values, inputs.names.map Prod.fst))) "entry owner change altered Core or parameter-only rows"
    for store in stores_variant do
      for fuel in List.range (bound + 3) do
        assertTrue (decide (runRuntimeFunction? types_variant2 selectedOwner source arguments fuel store =
          inputs.runTypedLetReturnBody? types_variant2 owner_variant fuel source.value.body store)) "entry owner change altered complete body execution"

def frontendParsedTypedLetReturnBodyOwnerTests : IO Unit := do
  have _ := shiftNotSurjective
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for (annotation, type) in [("Opaque", Core.Ty.namedData ⟨91⟩), ("Pkg.Token", .namedData ⟨92⟩), ("FnOpaque", .function .word (.namedData ⟨91⟩))] do
    for count in [0, 1, 2, 5, 12] do
      let indices := List.range count
      let declarations := String.join (indices.map fun index => s!"let z{index}: {annotation}=" ++ (if index = 0 then "x" else s!"z{index - 1}") ++ ";")
      let selected := if count = 0 then "x" else s!"z{count - 1}"
      let source ← parsed (Syntax.Parser.functionDecl .module) (s!"function nominal(x: {annotation},y: {annotation},c: Bool) returns ({annotation})" ++
        "{" ++ declarations ++ "if(c){if(c){return " ++ selected ++ ";}else{return y;}}else{return x;}}")
      let inputs ← declared source
      let terminal := Core.Expr.ifE (.var count) (.ifE (.var count) (.var (if count = 0 then 2 else 0)) (.var (count + 1))) (.var (count + 2))
      let core := indices.foldr (fun index tail => Core.Expr.letE (.var (if index = 0 then 2 else 0)) tail) terminal
      checkedStatic inputs source.value.body core type (3 * count + 7) 3
      assertTrue (decide (interpretRuntimeFunctionHeader? types_variant2 source.value.signature = some type)) "nominal header meaning changed"
      assertTrue (decide ((compileRuntimeFunction? types_variant2 owner_variant source).map (fun compiled =>
        (compiled.core, compiled.returnType, compiled.inputs.names, compiled.inputs.context.values)) =
          some (core, type, inputs.names, inputs.context.values))) "nominal compilation needed values or changed its original parameter rows"
  for (x, r) in [(word 9, word 2), (Core.Word.zero, Core.Word.maximum), (word (2 ^ 255), word 7)] do
    let args : List TypedRuntimeArgument := [⟨.word, .word x, .word⟩, ⟨.word, .word r, .word⟩]
    fixture "function ordered(x: Word,r: Word) returns (Word){let y: Word=x;let z: Word=y - r;return z;}" args
      (.letE (.var 1) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0))) .word (.word (x.sub r)) 11 11
    fixture "function unused(x: Word,r: Word) returns (Word){let z: Word=x - r;return x;}" args
      (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 2)) .word (.word x) 8 8
    for c in [false, true] do
      for d in [false, true] do
        fixture "function asymmetric(c: Bool,d: Bool,x: Word,r: Word) returns (Word){let y: Word=x;if(c){if(d){return ~y;}else{return y - r;}}else{return r;}}"
          ([⟨.bool, .bool c, .bool⟩, ⟨.bool, .bool d, .bool⟩] ++ args)
          (.letE (.var 1) (.ifE (.var 4) (.ifE (.var 3) (.unary .wordNot (.var 0)) (.binary .wordSub (.var 0) (.var 1))) (.var 1)))
          .word (.word (if c then if d then x.bitNot else x.sub r else r)) (if c then if d then 12 else 14 else 7) 14
  for (name, argument) in [("Cell", (⟨.cell .word, .cellRef .word 29, .cellRef⟩ : TypedRuntimeArgument)),
      ("Fn", ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩),
      ("Unit", ⟨.unit, .unit, .unit⟩), ("Bool", ⟨.bool, .bool false, .bool⟩)] do
    fixture (s!"function opaque(x: {name}) returns ({name})" ++ "{let y: " ++ name ++ "=x;let z: " ++ name ++ "=y;return z;}") [argument]
      (.letE (.var 0) (.letE (.var 0) (.var 0))) argument.type argument.value 7 7
  fixture "function emptyScope() returns (Word){let z: Word=7;return z;}" [] (.letE (.word (word 7)) (.var 0)) .word (.word (word 7)) 4 4
  let mixed : LocalInputs := ⟨[⟨"r", ⟨shift owner_variant, 500⟩, .word, .word (word 2), .word⟩,
    ⟨"x", ⟨owner_variant, 4⟩, .word, .word (word 9), .word⟩, ⟨"c", ⟨owner_variant, 40⟩, .bool, .bool true, .bool⟩], by decide⟩
  let mixedBody ← parsed (Syntax.Parser.block .allow) "{let y: Word=x;let z: Word=y - r;return z;}"
  assertTrue (decide (mixed.environment.values = [.word (word 2), .word (word 9), .bool true])) "mixed-owner fixture lost its independent actual order"
  let repeated := mixed.ids ++ [⟨owner_variant, 40⟩, ⟨shift owner_variant, 900⟩]
  have _ := Resolved.freshLocalId_map_owner shift shiftInjective owner_variant repeated
  assertTrue (decide (Resolved.freshLocalId owner_variant repeated = ⟨owner_variant, 41⟩ ∧
    Resolved.freshLocalId (shift owner_variant) (repeated.map mapping) = ⟨shift owner_variant, 41⟩)) "other owners, sparse indices or repeated raw IDs changed fresh allocation"
  runChecked mixed mixedBody (.letE (.var 1) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0))) .word (.word (word 7)) 11 11 41
  for body in ["{let z: Unknown=x;return z;}", "{let z: Bool=x;return z;}", "{let x: Word=r;return x;}",
      "{let z: Word=x;let z: Word=r;return z;}", "{let z=x;return z;}", "{let z: Word;return x;}",
      "{let z: Word=z;return x;}", "{let y: Word=z;let z: Word=x;return y;}",
      "{let z: Word=missing;return x;}", "{let z: Word=x();return x;}",
      "{let z: Word=x;if(c){if(c){return z;}else{return missing;}}else{return x;}}",
      "{let z: Word=x;if(c){return z;}else{return c;}}", "{let z: Word=x;if(x){return z;}else{return r;}}",
      "{let z: Word=x;if(c){return z;}}", "{let z: Word=x;if(c){let y: Word=z;return y;}else{return r;}}",
      "{let z: Word=x;return z;return x;}", "{}"] do
    let source ← parsed (Syntax.Parser.functionDecl .module) ("function rejected(x: Word,r: Word,c: Bool) returns (Word)" ++ body)
    let inputs ← actual_variant source [⟨.word, .word (word 9), .word⟩, ⟨.word, .word (word 2), .word⟩, ⟨.bool, .bool true, .bool⟩]
    let _ ← relabeled inputs.toTypeInputs source.value.body
    let mapped := inputs.mapIds mapping mappingInjective
    have _ := inputs.checkTypedLetReturnBody?_mapOwner shift shiftInjective types_variant2 owner_variant source.value.body
    assertTrue ((inputs.checkTypedLetReturnBody? types_variant2 owner_variant source.value.body).isNone &&
      (mapped.checkTypedLetReturnBody? types_variant2 (shift owner_variant) source.value.body).isNone) "owner change repaired whole rejection"
    for store in stores_variant do
      for fuel in List.range (typedLetReturnBodyFuelBound source.value.body + 3) do
        have _ := inputs.runTypedLetReturnBody?_mapOwner shift shiftInjective types_variant2 owner_variant fuel source.value.body store
        assertTrue ((inputs.runTypedLetReturnBody? types_variant2 owner_variant fuel source.value.body store).isNone &&
          (mapped.runTypedLetReturnBody? types_variant2 (shift owner_variant) fuel source.value.body store).isNone) "non-surjective owner relabeling or fuel repaired a rejected body"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTypedLetReturnBodyTypeExtensions
/-! Type dictionaries change, but parsed bodies and their originally declared
input rows do not. First-match preservation is stronger than retaining rows. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def owner_variant2 : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"PrefixTypes", by decide⟩], by decide⟩⟩, 17⟩
private def base : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
  (["Pkg", "Token"], .namedData ⟨92⟩), (["Pkg.Token"], .word), (["Word"], .bool)]
private def alternate : TypeNameTable := [(["Opaque"], .namedData ⟨91⟩), (["Fn"], .function .bool .bool),
  (["Unit"], .unit), (["Cell"], .cell .word), (["Bool"], .bool), (["Pkg.Token"], .word),
  (["Pkg", "Token"], .namedData ⟨92⟩), (["Word"], .word), (["Opaque"], .word), (["Word"], .unit)]
private def extras : TypeNameTable := [(["WordAlias"], .word), (["Alias"], .namedData ⟨91⟩), (["Word"], .bool)]
private def extended := base ++ extras
private theorem sameLookup (key : List String) : base.lookup? key = alternate.lookup? key := by
  by_cases w : ["Word"] = key
  · subst key; rfl
  by_cases b : ["Bool"] = key
  · subst key; rfl
  by_cases u : ["Unit"] = key
  · subst key; rfl
  by_cases c : ["Cell"] = key
  · subst key; rfl
  by_cases f : ["Fn"] = key
  · subst key; rfl
  by_cases o : ["Opaque"] = key
  · subst key; rfl
  by_cases q : ["Pkg", "Token"] = key
  · subst key; rfl
  by_cases flattened : ["Pkg.Token"] = key
  · subst key; rfl
  simp [base, alternate, TypeNameTable.lookup?, w, b, u, c, f, o, q, flattened]
private theorem fromLookup {old next : TypeNameTable}
    (same : ∀ key, old.lookup? key = next.lookup? key) : TypeNameTable.Extends old next := by
  intro key type found
  exact TypeNameTable.lookup?_iff.mp ((same key).symm.trans (TypeNameTable.lookup?_iff.mpr found))
private theorem forward : TypeNameTable.Extends base alternate := fromLookup sameLookup
private theorem backward : TypeNameTable.Extends alternate base := fromLookup (fun key => (sameLookup key).symm)
private theorem grows : TypeNameTable.Extends base extended := TypeNameTable.Extends.append_right base extras
private def parsed_variant {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO α := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-prefix-type-extensions.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := parser (Syntax.Parser.State.initial file lexed) | throw (IO.userError s!"fixture did not parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "incomplete or diagnosed source"
  return source
private def declared_variant (source : Syntax.FunctionDecl) : IO LocalTypeInputs := do
  let parameters := source.value.signature.parameters.elements
  match accepted : declareRuntimeParameters? base owner_variant2 parameters with
  | none => throw (IO.userError "original value-free source parameters did not declare")
  | some inputs =>
      have _ := declareRuntimeParameters?_sound accepted
      let rows := parameters.filterMap fun parameter => match parameter.value with
        | .typed none name annotation => (interpretTypeName? base annotation).map (name.value, ·)
        | _ => none
      assertTrue (decide (rows.length = parameters.length ∧ inputs.names.map Prod.fst = (rows.map Prod.fst).reverse ∧
        inputs.context.values = (rows.map Prod.snd).reverse ∧ inputs.ids =
          (List.range parameters.length).reverse.map (fun index => (⟨owner_variant2, index⟩ : Resolved.LocalId)))) "original parameter rows changed"
      return inputs
private def staticCheck (inputs : LocalTypeInputs) (body : Syntax.Block) (expected : Option (Core.Expr × Core.Ty)) : IO Unit := do
  have _ := elaborateTypedLetReturnBody?_eq_of_mutual_extends forward backward owner_variant2 inputs body
  assertTrue (decide (elaborateTypedLetReturnBody? base owner_variant2 inputs body = expected ∧
    elaborateTypedLetReturnBody? alternate owner_variant2 inputs body = expected)) "mutual extension changed an exact optional result"
  match accepted : elaborateTypedLetReturnBody? base owner_variant2 inputs body with
  | none => pure ()
  | some (core, type) =>
      have _ := (elaborateTypedLetReturnBody?_elaborates accepted).extend_types grows
      have _ := (elaborateTypedLetReturnBody?_sound accepted).extend_types grows
      have _ := elaborateTypedLetReturnBody?_some_of_extends grows accepted
      assertTrue (decide (elaborateTypedLetReturnBody? extended owner_variant2 inputs body = some (core, type) ∧
        Core.infer? inputs.context.values core = some type)) "one-way extension changed successful Core or type"
private def actual_variant2 (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO LocalInputs := do
  let static ← declared_variant source
  match accepted : bindRuntimeParameters? base owner_variant2 source.value.signature.parameters.elements arguments with
  | none => throw (IO.userError "original actual arguments did not bind")
  | some inputs =>
      have _ := (bindRuntimeParameters?_sound accepted).erase_values.complete
      assertTrue (decide (inputs.environment.values = (arguments.map (·.value)).reverse ∧
        inputs.names = static.names ∧ inputs.context = static.context)) "actual arguments changed declaration positions or values"
      return inputs
private def expectedObservation (observed : Option (Core.Ty × Core.StatefulRunResult))
    (type : Core.Ty) (value : Core.Value) (store : Core.Store) (cost fuel : Nat) : Bool :=
  match observed with
  | some (actualType, .done result finalStore) => decide (actualType = type ∧ result = value ∧ finalStore = store ∧ cost ≤ fuel)
  | some (actualType, .outOfFuel checkpoint) => decide (actualType = type ∧ checkpoint.store = store ∧ fuel < cost)
  | _ => false
private def runChecked_variant (inputs : LocalInputs) (body : Syntax.Block) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  staticCheck inputs.toTypeInputs body (some (core, type))
  have _ := inputs.checkTypedLetReturnBody?_eq_of_mutual_extends forward backward owner_variant2 body
  match checked : inputs.checkTypedLetReturnBody? base owner_variant2 body with
  | none => throw (IO.userError "positive body did not check")
  | some _ =>
      have _ := LocalInputs.checkTypedLetReturnBody?_some_of_extends grows checked
      assertTrue (decide (inputs.checkTypedLetReturnBody? extended owner_variant2 body = some (core, type) ∧
        typedLetReturnBodyFuelBound body = bound)) "checker extension or independent numerical bound changed"
  for store in stores_variant do
    let run := fun types fuel => inputs.runTypedLetReturnBody? types owner_variant2 fuel body store
    match core with
    | .letE initializer tail =>
        let checkpoint : Core.State := ⟨.eval initializer inputs.environment.values, [.letBody tail inputs.environment.values], store⟩
        assertTrue (decide (run base 1 = some (type, .outOfFuel checkpoint) ∧ run alternate 1 = run base 1 ∧ run extended 1 = run base 1))
          "dictionary change rewrote original values or the pending let frame"
    | _ => pure ()
    for fuel in List.range (bound + 3) do
      have sameResult := inputs.runTypedLetReturnBody?_eq_of_mutual_extends forward backward owner_variant2 fuel body store
      assertTrue (decide (run base fuel = run alternate fuel ∧
        run base fuel = some (type, Core.runStateful fuel (.initial core inputs.environment.values store)))) "mutual extension changed full execution"
      assertTrue (expectedObservation (run base fuel) type value store cost fuel) "independent value, store or cost threshold changed"
      match original : run base fuel with
      | none => throw (IO.userError "whole accepted body returned none")
      | some (actualType, result) =>
          have extendedAt := LocalInputs.runTypedLetReturnBody?_some_of_extends grows original
          have alternateAt := sameResult.symm.trans original
          assertTrue (decide (run extended fuel = some (actualType, result))) "one-way extension did not retain the full successful pair"
          match resultAt : result with
          | .outOfFuel checkpoint =>
              have originalOut : run base fuel = some (actualType, .outOfFuel checkpoint) := by
                simpa only [resultAt] using original
              have alternateOut : run alternate fuel = some (actualType, .outOfFuel checkpoint) := by
                simpa only [resultAt] using alternateAt
              have extendedOut : run extended fuel = some (actualType, .outOfFuel checkpoint) := by
                simpa only [resultAt] using extendedAt
              for remaining in List.range (cost - fuel + 3) do
                have _ := LocalInputs.runTypedLetReturnBody?_resume originalOut remaining
                have _ := LocalInputs.runTypedLetReturnBody?_resume alternateOut remaining
                have _ := LocalInputs.runTypedLetReturnBody?_resume extendedOut remaining
                assertTrue (decide (run base (fuel + remaining) = some (type, Core.runStateful remaining checkpoint) ∧
                  run alternate (fuel + remaining) = run base (fuel + remaining) ∧ run extended (fuel + remaining) = run base (fuel + remaining)))
                  "type extension rebuilt a genuine checkpoint or changed its resumption"
              assertTrue (decide (Core.runStateful (cost - fuel) checkpoint = .done value store)) "genuine residual changed its expected value"
          | _ => pure ()
private def fixture_variant (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let source ← parsed_variant (Syntax.Parser.functionDecl .module) content
  let inputs ← actual_variant2 source arguments
  assertTrue (decide (interpretRuntimeFunctionHeader? base source.value.signature = some type)) "body used a wrong header contrast"
  runChecked_variant inputs source.value.body core type value cost bound
  for names in [base, alternate, extended] do
    assertTrue (decide ((compileRuntimeFunction? names owner_variant2 source).map (fun compiled =>
      (compiled.core, compiled.returnType, compiled.inputs.names, compiled.inputs.context.values)) =
        some (core, type, inputs.names, inputs.context.values))) "entry dictionary extension changed exact Core or original parameter-only rows"
    for store in stores_variant do
      for fuel in List.range (bound + 3) do
        assertTrue (decide (runRuntimeFunction? names owner_variant2 source arguments fuel store =
          inputs.runTypedLetReturnBody? base owner_variant2 fuel source.value.body store)) "entry dictionary extension changed complete body execution"

def frontendParsedTypedLetReturnBodyTypeExtensionTests : IO Unit := do
  assertTrue (decide (base ≠ alternate ∧ base.length ≠ alternate.length)) "different hidden rows or dictionary ordering became trivial"
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for (annotation, type) in [("Opaque", Core.Ty.namedData ⟨91⟩), ("Pkg.Token", .namedData ⟨92⟩)] do
    for count in [0, 1, 2, 5, 12] do
      let indices := List.range count
      let declarations := String.join (indices.map fun index => s!"let z{index}: {annotation}=" ++ (if index = 0 then "x" else s!"z{index - 1}") ++ ";")
      let selected := if count = 0 then "x" else s!"z{count - 1}"
      let source ← parsed_variant (Syntax.Parser.functionDecl .module) (s!"function nominal(x: {annotation},y: {annotation},c: Bool) returns ({annotation})" ++
        "{" ++ declarations ++ "if(c){if(c){return " ++ selected ++ ";}else{return y;}}else{return x;}}")
      let inputs ← declared_variant source
      let terminal := Core.Expr.ifE (.var count) (.ifE (.var count) (.var (if count = 0 then 2 else 0)) (.var (count + 1))) (.var (count + 2))
      let core := indices.foldr (fun index tail => Core.Expr.letE (.var (if index = 0 then 2 else 0)) tail) terminal
      staticCheck inputs source.value.body (some (core, type))
      assertTrue (decide (typedLetReturnBodyFuelBound source.value.body = 3 * count + 7)) "nominal numeric bound required an inhabitant"
  for (x, r) in [(word 9, word 2), (Core.Word.zero, Core.Word.maximum), (word (2 ^ 255), word 7)] do
    let args : List TypedRuntimeArgument := [⟨.word, .word x, .word⟩, ⟨.word, .word r, .word⟩]
    fixture_variant "function ordered(x: Word,r: Word) returns (Word){let y: Word=x;let z: Word=y - r;return z;}" args
      (.letE (.var 1) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0))) .word (.word (x.sub r)) 11 11
    fixture_variant "function unused(x: Word,r: Word) returns (Word){let z: Word=x - r;return x;}" args
      (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 2)) .word (.word x) 8 8
    for c in [false, true] do
      for d in [false, true] do
        fixture_variant "function asymmetric(c: Bool,d: Bool,x: Word,r: Word) returns (Word){let y: Word=x;if(c){if(d){return ~y;}else{return y - r;}}else{return r;}}"
          ([⟨.bool, .bool c, .bool⟩, ⟨.bool, .bool d, .bool⟩] ++ args)
          (.letE (.var 1) (.ifE (.var 4) (.ifE (.var 3) (.unary .wordNot (.var 0)) (.binary .wordSub (.var 0) (.var 1))) (.var 1)))
          .word (.word (if c then if d then x.bitNot else x.sub r else r)) (if c then if d then 12 else 14 else 7) 14
  for (name, argument) in [("Cell", (⟨.cell .word, .cellRef .word 29, .cellRef⟩ : TypedRuntimeArgument)),
      ("Fn", ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩),
      ("Unit", ⟨.unit, .unit, .unit⟩), ("Bool", ⟨.bool, .bool false, .bool⟩)] do
    fixture_variant (s!"function opaque(x: {name}) returns ({name})" ++ "{let y: " ++ name ++ "=x;let z: " ++ name ++ "=y;return z;}") [argument]
      (.letE (.var 0) (.letE (.var 0) (.var 0))) argument.type argument.value 7 7
  for body in ["{let z: Unknown=x;return z;}", "{let z: Bool=x;return z;}", "{let x: Word=x;return x;}",
      "{let z: Word=x;let z: Word=x;return z;}", "{let z=x;return z;}", "{let z: Word;return x;}",
      "{let z: Word=z;return x;}", "{let y: Word=z;let z: Word=x;return y;}", "{let z: Word=missing;return x;}",
      "{let z: Word=x();return x;}", "{let z: Word<Bool> = x;return x;}",
      "{let z: Word=x;if(c){if(c){return z;}else{return missing;}}else{return x;}}",
      "{let z: Word=x;if(c){return z;}else{return c;}}", "{let z: Word=x;if(x){return z;}else{return x;}}",
      "{let z: Word=x;if(c){return z;}}", "{let z: Word=x;if(c){let y: Word=z;return y;}else{return x;}}", "{}"] do
    let source ← parsed_variant (Syntax.Parser.functionDecl .module) ("function rejected(x: Word,c: Bool) returns (Word)" ++ body)
    let inputs ← actual_variant2 source [⟨.word, .word (word 9), .word⟩, ⟨.bool, .bool true, .bool⟩]
    staticCheck inputs.toTypeInputs source.value.body none
    have _ := inputs.checkTypedLetReturnBody?_eq_of_mutual_extends forward backward owner_variant2 source.value.body
    for store in stores_variant do
      for fuel in List.range (typedLetReturnBodyFuelBound source.value.body + 3) do
        have _ := inputs.runTypedLetReturnBody?_eq_of_mutual_extends forward backward owner_variant2 fuel source.value.body store
        assertTrue ((inputs.runTypedLetReturnBody? base owner_variant2 fuel source.value.body store).isNone &&
          (inputs.runTypedLetReturnBody? alternate owner_variant2 fuel source.value.body store).isNone) "mutual dictionaries repaired whole rejection"
  let qualified ← parsed_variant Syntax.Parser.typeExpr "Pkg /* exact components */ . Token"
  let .named name none := qualified.value | throw (IO.userError "qualified annotation changed shape")
  assertTrue (decide (qualifiedTypeNameKey name = ["Pkg", "Token"] ∧ interpretTypeName? base qualified = some (.namedData ⟨92⟩) ∧
    base.lookup? ["Pkg.Token"] = some .word ∧ alternate.lookup? ["Pkg", "Token"] = some (.namedData ⟨92⟩))) "qualified keys were flattened"
  let nominal ← parsed_variant (Syntax.Parser.functionDecl .module) "function repair(x: Opaque) returns (Opaque){let z: Alias=x;return z;}"
  let nominalInputs ← declared_variant nominal
  staticCheck nominalInputs nominal.value.body none
  assertTrue (decide (elaborateTypedLetReturnBody? extended owner_variant2 nominalInputs nominal.value.body =
    some (.letE (.var 0) (.var 0), .namedData ⟨91⟩))) "new nominal meaning needed a fabricated actual value"
  let repaired ← parsed_variant (Syntax.Parser.functionDecl .module) "function repair(x: Word) returns (Word){let z: WordAlias=x;return z;}"
  let fixed ← actual_variant2 repaired [⟨.word, .word (word 9), .word⟩]
  staticCheck fixed.toTypeInputs repaired.value.body none
  assertTrue (decide (fixed.ids = [⟨owner_variant2, 0⟩] ∧ fixed.context.values = [.word] ∧ fixed.environment.values = [.word (word 9)] ∧
    fixed.checkTypedLetReturnBody? extended owner_variant2 repaired.value.body = some (.letE (.var 0) (.var 0), .word) ∧
    typedLetReturnBodyFuelBound repaired.value.body = 4)) "repair changed fixed inputs or numerical cost"
  for store in stores_variant do
    for fuel in List.range 7 do
      assertTrue ((fixed.runTypedLetReturnBody? base owner_variant2 fuel repaired.value.body store).isNone &&
        expectedObservation (fixed.runTypedLetReturnBody? extended owner_variant2 fuel repaired.value.body store) .word (.word (word 9)) store 4 fuel)
        "one-way extension incorrectly preserved none or changed repaired execution"
  let shadow : TypeNameTable := (["Word"], .bool) :: base
  have _ : ¬ TypeNameTable.Extends base shadow := by
    intro extension
    have impossible := (extension (show TypeNameTable.Lookup base ["Word"] .word from .head)).type_unique (show TypeNameTable.Lookup shadow ["Word"] .bool from .head)
    cases impossible
  have _ : ∀ row ∈ base, row ∈ shadow := fun _ member => List.mem_cons_of_mem _ member
  let shadowed ← parsed_variant (Syntax.Parser.functionDecl .module) "function shadow(x: Word) returns (Word){let z: Word=x;return z;}"
  assertTrue (decide (fixed.checkTypedLetReturnBody? base owner_variant2 shadowed.value.body = some (.letE (.var 0) (.var 0), .word) ∧
    fixed.checkTypedLetReturnBody? shadow owner_variant2 shadowed.value.body = none ∧ fixed.context.values = [.word] ∧
    fixed.environment.values = [.word (word 9)] ∧ shadow.drop 1 = base)) "retaining dictionary rows was mistaken for first-match extension"
  let untouched ← parsed_variant (Syntax.Parser.block .allow) "{return x;}"
  assertTrue (decide (fixed.checkTypedLetReturnBody? shadow owner_variant2 untouched = some (.var 0, .word))) "changed dictionary silently redeclared the fixed input bundle"
  for store in stores_variant do
    for fuel in List.range 7 do
      assertTrue ((fixed.runTypedLetReturnBody? shadow owner_variant2 fuel shadowed.value.body store).isNone) "changed-head rejection was repaired by fuel"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTypedLetRuntimeEntries
/-! Compile completely parsed prefixes once, then run actual arguments against
independent Core, typed value and source-cost expectations. Prefix locals are
never parameters; actual checkpoints retain their captured original values. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def owner_variant3 : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"PrefixEntries", by decide⟩], by decide⟩⟩, 17⟩
private def otherOwner : Resolved.DeclarationId := { owner_variant3 with declarationIndex := 71 }
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, .word (word n), .word⟩
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def types_variant3 : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
  (["Pkg", "Token"], .namedData ⟨92⟩), (["Pkg.Token"], .bool)]
private def extras_variant : TypeNameTable := [(["Word"], .bool), (["Fresh"], .namedData ⟨93⟩)]
private def extended_variant := types_variant3 ++ extras_variant
private theorem grows_variant : TypeNameTable.Extends types_variant3 extended_variant := TypeNameTable.Extends.append_right types_variant3 extras_variant
private def parsed_variant? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-prefix-entries.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next => return if next.atEnd && next.diagnostics.isEmpty then some source else none
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "parser invariant")
private structure Entry where
  source : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction
  provenance : RuntimeFunctionCompiles types_variant3 owner_variant3 source compiled
  oldPrefix : Bool
private theorem excludeWrong_variant {source : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (provenance : RuntimeFunctionCompiles types_variant3 owner_variant3 source compiled) {wrong : Core.Expr} (different : wrong ≠ compiled.core) :
    ¬ RuntimeFunctionCompiles types_variant3 owner_variant3 source { compiled with core := wrong } := by
  intro other
  exact different (congrArg CompiledRuntimeFunction.core (other.result_unique provenance))
private def compile (content : String) (core : Core.Expr) (type : Core.Ty) (parameterTypes : List Core.Ty) (bound : Nat)
    (oldPrefix : Bool := true) : IO Entry := do
  let some source ← parsed_variant? content | throw (IO.userError "positive whole declaration did not completely parse")
  match accepted : compileRuntimeFunction? types_variant3 owner_variant3 source with
  | none => throw (IO.userError "valid typed-prefix entry did not compile")
  | some compiled =>
      let provenance := compileRuntimeFunction?_sound accepted
      let names ← source.value.signature.parameters.elements.mapM fun parameter => do
        let .typed none name annotation := parameter.value | throw (IO.userError "unexpected parameter shape")
        assertTrue (parameter.span.contains name.span && parameter.span.contains annotation.span && source.span.contains parameter.span)
          "source parameter positions changed"
        pure name.value
      assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧ compiled.inputs.context.values = parameterTypes.reverse ∧
        compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner_variant3, index⟩ : Resolved.LocalId)))).reverse ∧
        compiled.inputs.bindings.length = parameterTypes.length ∧ Core.infer? parameterTypes.reverse core = some type ∧
        typedLetReturnTreeFuelBound source.value.body = bound ∧ terminalReturnTreeFuelBound source.value.body = 0))
        "compiled prefix changed exact Core/type/bound or leaked locals into original parameter rows"
      if oldPrefix then assertTrue (typedLetReturnBodyFuelBound source.value.body == bound) "old successful prefix bound changed"
      assertTrue ((elaborateTerminalReturnTree? compiled.inputs.names compiled.inputs.context source.value.body).isNone)
        "entry integration broadened the old tree adapter"
      have _ := provenance.core_hasType
      have _ := provenance.extend_types grows_variant
      have _ := compileRuntimeFunction?_some_of_extends grows_variant accepted
      assertTrue (decide ((compileRuntimeFunction? extended_variant owner_variant3 source).map (fun changed =>
        (changed.core, changed.returnType, changed.inputs.names, changed.inputs.context.values)) =
          some (core, type, compiled.inputs.names, parameterTypes.reverse))) "type extension changed the exact compiled record"
      let wrong := Core.Expr.ifE (.bool true) core core
      if different : wrong ≠ compiled.core then
        have _ := excludeWrong_variant provenance different
        assertTrue (decide (Core.infer? parameterTypes.reverse wrong = some type)) "wrong-Core contrast was not equally typed"
      else throw (IO.userError "wrong-Core contrast became identical")
      return ⟨source, compiled, provenance, oldPrefix⟩
private def observation (observed : Option (Core.Ty × Core.StatefulRunResult))
    (expected : TypedRuntimeArgument) (store : Core.Store) (cost fuel : Nat) : Bool :=
  match observed with
  | some (type, .done value finalStore) => decide (type = expected.type ∧ value = expected.value ∧ finalStore = store ∧ cost ≤ fuel)
  | some (type, .outOfFuel checkpoint) => decide (type = expected.type ∧ checkpoint.store = store ∧ fuel < cost)
  | _ => false
private def checkCase (entry : Entry) (arguments : List TypedRuntimeArgument) (expected : TypedRuntimeArgument) (cost : Nat) : IO Unit := do
  let bound := typedLetReturnTreeFuelBound entry.source.value.body
  assertTrue (decide (expected.type = entry.compiled.returnType ∧ 0 < cost ∧ cost ≤ bound)) "independent value type or source cost disagreed"
  if matching : arguments.map (·.type) = entry.compiled.inputs.context.values.reverse then
    match preparedAt : prepareRuntimeFunction? types_variant3 owner_variant3 entry.source arguments with
    | none => throw (IO.userError "matching actual arguments did not prepare")
    | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      have _ := entry.provenance.prepare_arguments arguments matching
      have _ := prepareRuntimeFunction?_factorization types_variant3 owner_variant3 entry.source arguments
      assertTrue (decide (prepared.core = entry.compiled.core ∧ prepared.returnType = expected.type ∧
        prepared.inputs.names = entry.compiled.inputs.names ∧ prepared.inputs.context.values = entry.compiled.inputs.context.values ∧
        prepared.inputs.environment.values = arguments.reverse.map (·.value) ∧ prepared.inputs.bindings.length = arguments.length ∧
        prepared.inputs.checkTypedLetReturnTree? types_variant3 owner_variant3 entry.source.value.body = some (entry.compiled.core, expected.type)))
        "preparation rebound prefix locals as parameters or changed original ordered actual values"
      if entry.oldPrefix then assertTrue (decide (prepared.inputs.checkTypedLetReturnBody? types_variant3 owner_variant3 entry.source.value.body =
        some (entry.compiled.core, expected.type))) "old successful prefix checker changed"
      for store in stores_variant do
        have _ := entry.provenance.run_done_of_fuelBound arguments matching store bound (Nat.le_refl _)
        have _ := preparation.hasType.run_done_of_fuelBound store bound (Nat.le_refl _)
        let initial := Core.State.initial entry.compiled.core (arguments.reverse.map (·.value)) store
        let run := fun fuel => runRuntimeFunction? types_variant3 owner_variant3 entry.source arguments fuel store
        match entry.compiled.core with
        | .letE initializer tail =>
            let checkpoint : Core.State := ⟨.eval initializer (arguments.reverse.map (·.value)), [.letBody tail (arguments.reverse.map (·.value))], store⟩
            assertTrue (decide (run 1 = some (expected.type, .outOfFuel checkpoint))) "entry charged wrapper steps or lost its original pending let frame"
        | _ => throw (IO.userError "prefix compiled without ordered Core lets")
        for fuel in List.range (bound + 3) do
          have _ := entry.provenance.run_eq arguments matching fuel store
          have _ := (entry.provenance.extend_types grows_variant).run_eq arguments matching fuel store
          have _ := runRuntimeFunction?_factorization types_variant3 owner_variant3 entry.source arguments fuel store
          have _ := runRuntimeFunction?_owner_eq types_variant3 owner_variant3 otherOwner entry.source arguments fuel store
          assertTrue (decide (run fuel = some (expected.type, Core.runStateful fuel initial) ∧
            run fuel = prepared.inputs.runTypedLetReturnTree? types_variant3 owner_variant3 fuel entry.source.value.body store ∧
            run fuel = runRuntimeFunction? extended_variant owner_variant3 entry.source arguments fuel store ∧
            run fuel = runRuntimeFunction? types_variant3 otherOwner entry.source arguments fuel store)) "entry factorization, owner or table extension changed the full result"
          if entry.oldPrefix then
            assertTrue (decide (run fuel = prepared.inputs.runTypedLetReturnBody? types_variant3 owner_variant3 fuel entry.source.value.body store))
              "old successful prefix full same-fuel result changed"
          assertTrue (observation (run fuel) expected store cost fuel) "entry changed independent value, cost threshold or own store"
          for replacement in stores_variant do
            have _ := runRuntimeFunction?_done_store_iff types_variant3 owner_variant3 entry.source arguments fuel store replacement expected.type expected.value
            have _ := runRuntimeFunction?_outOfFuel_store_iff types_variant3 owner_variant3 entry.source arguments fuel store replacement expected.type
            assertTrue (observation (runRuntimeFunction? types_variant3 owner_variant3 entry.source arguments fuel replacement) expected replacement cost fuel)
              "store replay changed independent observation"
            if replacement != store then
              assertTrue (decide (run fuel ≠ runRuntimeFunction? types_variant3 owner_variant3 entry.source arguments fuel replacement))
                "distinct stores disappeared from complete results"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (type, .outOfFuel checkpoint) =>
              have _ := runRuntimeFunction?_eq_some_compiled_iff.mp exhausted
              assertTrue (decide (Core.runStateful 0 checkpoint = .outOfFuel checkpoint)) "a genuine checkpoint lost pending work"
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (type, Core.runStateful remaining checkpoint))) "genuine entry resumption changed"
                assertTrue (observation (some (type, Core.runStateful remaining checkpoint)) expected store (cost - spent) remaining)
                  "actual residual threshold disagreed with independent source cost"
              if spent + 1 < cost then
                let .outOfFuel next := Core.runStateful 1 checkpoint | throw (IO.userError "second genuine checkpoint disappeared")
                for last in [0, cost - spent - 1, cost - spent + 1] do
                  assertTrue (decide (run (spent + 1 + last) = some (type, Core.runStateful last next))) "three actual chunks changed their complete result"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (expected.type, .done expected.value store) ∧
                Core.runStateful (cost - spent) checkpoint = .done expected.value store)) "restarting the entry was mistaken for resumption"
          | _ => throw (IO.userError "expected a genuine checkpoint below independent source cost")
  else throw (IO.userError "positive fixture supplied wrong argument types")
private def rejectArguments (entry : Entry) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) ≠ entry.compiled.inputs.context.values.reverse)) "argument guard contrast became matching"
  for store in stores_variant do
    for fuel in [0, typedLetReturnTreeFuelBound entry.source.value.body, 60] do
      have _ := runRuntimeFunction?_factorization types_variant3 owner_variant3 entry.source arguments fuel store
      assertTrue ((prepareRuntimeFunction? types_variant3 owner_variant3 entry.source arguments).isNone &&
        (runRuntimeFunction? types_variant3 owner_variant3 entry.source arguments fuel store).isNone) "invalid actual arity/type produced a checkpoint"
private def reject (source : Syntax.FunctionDecl) : IO Unit := do
  assertTrue (compileRuntimeFunction? types_variant3 owner_variant3 source).isNone "invalid whole entry compiled"
  for arguments in [[], [wordArg 9], [wordArg 9, boolArg true], [wordArg 9, wordArg 2]] do
    for store in stores_variant do
      for fuel in [0, typedLetReturnTreeFuelBound source.value.body, 60] do
        assertTrue ((prepareRuntimeFunction? types_variant3 owner_variant3 source arguments).isNone &&
          (runRuntimeFunction? types_variant3 owner_variant3 source arguments fuel store).isNone) "whole rejection depended on arguments, store or fuel"

def frontendParsedTypedLetRuntimeEntryTests : IO Unit := do
  for count in [1, 2, 5, 12] do
    let indices := List.range count
    let prefixText := String.join (indices.map fun index => s!"let z{index}: Word=" ++ (if index = 0 then "x" else s!"z{index - 1}") ++ ";")
    let core := indices.foldr (fun index tail => Core.Expr.letE (.var (if index = 0 then 1 else 0)) tail) (.var 0)
    let entry ← compile ("function chain(x: Word,unused: Bool) returns (Word){" ++ prefixText ++ s!"return z{count - 1};" ++ "}") core .word [.word, .bool] (3 * count + 1)
    for value in [0, 9, Core.Word.maximum.val] do
      for flag in [false, true] do checkCase entry [wordArg value, boolArg flag] (wordArg value) (3 * count + 1)
    for arguments in [[], [wordArg 9], [boolArg true, wordArg 9], [wordArg 9, boolArg true, wordArg 7]] do rejectArguments entry arguments
  let ordered ← compile "function ordered(x: Word,r: Word) returns (Word){let y: Word=x;let z: Word=y - r;return z;}"
    (.letE (.var 1) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0))) .word [.word, .word] 11
  let unused ← compile "function unused(x: Word,r: Word) returns (Word){let z: Word=x - r;return x;}"
    (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 2)) .word [.word, .word] 8
  let asymmetric ← compile "function asymmetric(c: Bool,d: Bool,x: Word,r: Word) returns (Word){let y: Word=x;if(c){if(d){return ~y;}else{return y - r;}}else{return r;}}"
    (.letE (.var 1) (.ifE (.var 4) (.ifE (.var 3) (.unary .wordNot (.var 0)) (.binary .wordSub (.var 0) (.var 1))) (.var 1))) .word [.bool, .bool, .word, .word] 14
  for (x, r) in [(9, 2), (2, 9), (0, Core.Word.maximum.val), (2 ^ 255, 7)] do
    checkCase ordered [wordArg x, wordArg r] ⟨.word, .word ((word x).sub (word r)), .word⟩ 11
    checkCase unused [wordArg x, wordArg r] (wordArg x) 8
    for c in [false, true] do
      for d in [false, true] do
        checkCase asymmetric [boolArg c, boolArg d, wordArg x, wordArg r]
          ⟨.word, .word (if c then if d then (word x).bitNot else (word x).sub (word r) else word r), .word⟩
          (if c then if d then 12 else 14 else 7)
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let closure : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let captured : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, left, right) in [("Cell", (⟨.cell .word, .cellRef .word 17, .cellRef⟩ : TypedRuntimeArgument), ⟨.cell .word, .cellRef .word 29, .cellRef⟩),
      ("Fn", closure, captured), ("Bool", boolArg true, boolArg false), ("Unit", unit, unit)] do
    let entry ← compile (s!"function opaque(x: {name},y: {name}) returns ({name})" ++ "{let a: " ++ name ++ "=y;let b: " ++ name ++ "=x;return a;}")
      (.letE (.var 0) (.letE (.var 2) (.var 1))) left.type [left.type, right.type] 7
    checkCase entry [left, right] right 7
    checkCase entry [right, left] left 7
  let constant ← compile "function constant() returns (Word){let z: Word=7;return z;}" (.letE (.word (word 7)) (.var 0)) .word [] 4
  checkCase constant [] (wordArg 7) 4
  rejectArguments constant [wordArg 7]
  let branch ← compile "function branch(x: Word,c: Bool) returns (Word){let z: Word=x;if(c){let y: Word=z;return y;}else{return x;}}"
    (.letE (.var 1) (.ifE (.var 1) (.letE (.var 0) (.var 0)) (.var 2))) .word [.word, .bool] 10 false
  assertTrue (typedLetReturnBodyFuelBound branch.source.value.body == 7 &&
    (elaborateTypedLetReturnBody? types_variant3 owner_variant3 branch.compiled.inputs branch.source.value.body).isNone) "old prefix adapter or bound changed"
  for c in [false, true] do checkCase branch [wordArg 9, boolArg c] (wordArg 9) (if c then 10 else 7)
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for (name, type) in [("Opaque", Core.Ty.namedData ⟨91⟩), ("Pkg.Token", .namedData ⟨92⟩)] do
    for count in [1, 3, 8] do
      let indices := List.range count
      let prefixText := String.join (indices.map fun index => s!"let z{index}: {name}=" ++ (if index = 0 then "x" else s!"z{index - 1}") ++ ";")
      let terminal := Core.Expr.ifE (.var count) (.ifE (.var count) (.var 0) (.var (count + 1))) (.var (count + 1))
      let core := indices.foldr (fun index tail => Core.Expr.letE (.var (if index = 0 then 1 else 0)) tail) terminal
      let entry ← compile (s!"function nominal(x: {name},c: Bool) returns ({name})" ++ "{" ++ prefixText ++
        "if(c){if(c){return " ++ s!"z{count - 1}" ++ ";}else{return x;}}else{return x;}}") core type [type, .bool] (3 * count + 7)
      for argument in [wordArg 9, boolArg true, unit, captured, (⟨.cell .word, .cellRef .word 17, .cellRef⟩ : TypedRuntimeArgument)] do
        rejectArguments entry [argument, boolArg true]
  let validBody := "{let z: Word=7;return z;}"
  for header in ["function generic<T>() returns (Word)", "function many() returns (Word,Bool)", "function empty() returns ()",
      "function unknown() returns (Unknown)", "function duplicate(x: Word,x: Bool) returns (Word)",
      "function staged(comptime x: Word) returns (Word)", "function unknownParameter(x: Unknown) returns (Word)",
      "function wrong() returns (Bool)", "function absent()"] do
    let some source ← parsed_variant? (header ++ validBody) | throw (IO.userError "header/parameter rejection did not parse")
    assertTrue (decide (LocalInputs.empty.checkTypedLetReturnBody? types_variant3 owner_variant3 source.value.body =
      some (.letE (.word (word 7)) (.var 0), .word))) "header/parameter contrast did not retain an independently valid body"
    reject source
  let inferred ← compile "function invalid(x: Word,c: Bool) returns (Word){let z=x;return z;}"
    (.letE (.var 1) (.var 0)) .word [.word, .bool] 4 false
  assertTrue (typedLetReturnBodyFuelBound inferred.source.value.body == 0 &&
    (elaborateTypedLetReturnBody? types_variant3 owner_variant3 inferred.compiled.inputs inferred.source.value.body).isNone) "old annotated prefix boundary changed"
  checkCase inferred [wordArg 9, boolArg true] (wordArg 9) 4
  for arguments in [[], [wordArg 9], [wordArg 9, wordArg 2]] do rejectArguments inferred arguments
  for body in ["{let z: Word;return x;}", "{let z: Unknown=x;return x;}", "{let z: Bool=x;return x;}",
      "{let x: Word=x;return x;}", "{let z: Word=x;let z: Word=x;return z;}", "{let z: Word=z;return x;}",
      "{let y: Word=z;let z: Word=x;return y;}", "{let z: Word=missing;return x;}", "{let z: Word=x();return x;}",
      "{let z: Word=c ? x : missing;return x;}", "{let z: Word=x;if(c){if(c){return z;}else{return missing;}}else{return x;}}",
      "{let z: Word=x;if(c){return z;}else{return c;}}", "{let z: Word=x;if(x){return z;}else{return x;}}",
      "{let z: Word=x;if(c){return z;}}",
      "{let z: Word=x;return z;return x;}", "{let z: Word=x;z=x;return z;}", "{}"] do
    let some source ← parsed_variant? ("function invalid(x: Word,c: Bool) returns (Word)" ++ body) | throw (IO.userError "bad-prefix fixture did not parse")
    assertTrue (decide (interpretRuntimeFunctionHeader? types_variant3 source.value.signature = some .word) &&
      (bindRuntimeParameters? types_variant3 owner_variant3 source.value.signature.parameters.elements [wordArg 9, boolArg true]).isSome)
      "bad-prefix rejection was caused by header or parameters"
    reject source
  for content in ["function missing(x){let z: Word=7;return z;}", "function incomplete(){let z: Word=;return z;}",
      "function incomplete(){let z: Word=7;return z;", "function trailing(){let z: Word=7;return z;} trailing"] do
    assertTrue (← parsed_variant? content).isNone "incomplete source acquired entry meaning"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendTypedLetReturnBodyEvaluationProperties
/-! Independent let paths use actual values and count even unused initializers.
Static typing, positional alignment and pending-continuation safety are separate. -/

set_option autoImplicit false

namespace Tests.FrontendTypedLetReturnBodyEvaluation

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetEvaluation", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-evaluation.sol"⟩, 141, 5⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def binding (name : String) (value : Syntax.Expr) : Syntax.Statement :=
  ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some value)⟩
private def returned (value : Syntax.Expr) : Syntax.Statement := ⟨span, .returnStmt (some value)⟩
private def statements : List String → String → List Syntax.Statement
  | [], previous => [returned (ref previous)]
  | name :: rest, previous => binding name (ref previous) :: statements rest name
private def chain (names : List String) (previous : String) : Syntax.Block := ⟨span, statements names previous⟩
private def inputs (type : Core.Ty) : LocalTypeInputs := LocalTypeInputs.empty.bindFresh owner "seed" type
private def table : LocalNameTable := [("seed", id 0)]
private def environment (value : Core.Value) : Resolved.Environment := [(id 0, value)]
private def one := chain ["x"] "seed"
private def oneCore : Core.Expr := .letE (.var 0) (.var 0)

private theorem chainRaw (names : List String) (previous : String) (namesTable : LocalNameTable)
    (values : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluates namesTable values store (ref previous) value store) :
    TypedLetReturnBodyEvaluates owner namesTable values store (chain names previous) value store := by
  induction names generalizing previous namesTable values with
  | nil => exact .terminal (.single (.expression head))
  | cons name rest ih => exact .binding head (ih name _ _ (.identifier .head .head))
private theorem chainCost (names : List String) (previous : String) (namesTable : LocalNameTable)
    (values : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost namesTable values store (ref previous) value store 1) :
    TypedLetReturnBodyEvaluatesWithCost owner namesTable values store (chain names previous) value store (3 * names.length + 1) := by
  induction names generalizing previous namesTable values with
  | nil => exact .terminal (.single (.expression head))
  | cons name rest ih =>
      have arithmetic : 1 + (3 * rest.length + 1) + 2 = 3 * (name :: rest).length + 1 := by simp; omega
      simpa only [arithmetic, chain, statements, binding] using
        TypedLetReturnBodyEvaluatesWithCost.binding (name := ⟨span, name⟩) (annotation := annotation)
          head (ih name _ _ (.identifier .head .head))
private theorem counted (value : Core.Value) (store : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner table (environment value) store one value store 4 :=
  chainCost ["x"] "seed" table (environment value) value store (.identifier .head .head)
private theorem elaborated (type : Core.Ty) :
    TypedLetReturnBodyElaborates (types type) owner (inputs type) one oneCore type :=
  .binding (.named .head) (by change "x" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
    (.terminal (.single (.expression (.identifier .head) (.var .head) (.var .head))))

theorem independent_static_provenance_requires_neither_a_value_nor_a_store (type : Core.Ty) :
    TypedLetReturnBodyElaborates (types type) owner (inputs type) one oneCore type ∧
    elaborateTypedLetReturnBody? (types type) owner (inputs type) one = some (oneCore, type) :=
  ⟨elaborated type, (elaborated type).complete⟩

theorem arbitrary_lists_need_no_name_freshness_or_runtime_type_to_have_independent_raw_cost
    (names : List String) (value : Core.Value) (store : Core.Store) :
    TypedLetReturnBodyEvaluates owner table (environment value) store (chain names "seed") value store ∧
    TypedLetReturnBodyEvaluatesWithCost owner table (environment value) store (chain names "seed") value store (3 * names.length + 1) :=
  ⟨chainRaw names "seed" table (environment value) value store (.identifier .head .head),
    chainCost names "seed" table (environment value) value store (.identifier .head .head)⟩

theorem independent_paths_determine_exact_positive_cost_and_keep_each_store
    (names : List String) (value rawValue countedValue : Core.Value) (store rawStore countedStore : Core.Store) (cost : Nat)
    (raw : TypedLetReturnBodyEvaluates owner table (environment value) store (chain names "seed") rawValue rawStore)
    (costed : TypedLetReturnBodyEvaluatesWithCost owner table (environment value) store (chain names "seed") countedValue countedStore cost) :
    rawValue = value ∧ rawStore = store ∧ countedValue = value ∧ countedStore = store ∧ cost = 3 * names.length + 1 ∧ 0 < cost ∧
    (∃ witness, TypedLetReturnBodyEvaluatesWithCost owner table (environment value) store (chain names "seed") rawValue rawStore witness) ∧
    (TypedLetReturnBodyEvaluates owner table (environment value) store (chain names "seed") value store ↔
      ∃ witness, TypedLetReturnBodyEvaluatesWithCost owner table (environment value) store (chain names "seed") value store witness) := by
  have original := chainCost names "seed" table (environment value) value store (.identifier .head .head)
  have same := costed.deterministic original
  exact ⟨(raw.deterministic original.erase).1, raw.store_eq, same.1, costed.store_eq, same.2.2, costed.cost_pos,
    raw.exists_cost, typedLetReturnBodyEvaluates_iff_exists_cost⟩

theorem arbitrary_static_types_do_not_supply_values_but_actual_typed_values_supply_existence
    (type : Core.Ty) (actual result : Core.Value) (typed : Core.ValueHasType actual type) (store finalStore : Core.Store)
    (raw : TypedLetReturnBodyEvaluates owner table (environment actual) store one result finalStore) :
    elaborateTypedLetReturnBody? (types type) owner (inputs type) one = some (oneCore, type) ∧
    (inputs type).names.map Prod.snd = (inputs type).ids ∧
    (∃ value, TypedLetReturnBodyEvaluates owner table (environment actual) store one value store ∧ Core.ValueHasType value type) ∧
    Core.ValueHasType result type ∧ finalStore = store := by
  have sourceType := (elaborated type).hasType
  have actualTypes : Core.EnvironmentHasTypes (environment actual).values (inputs type).context.values := .cons typed .nil
  exact ⟨(elaborated type).complete, (inputs type).names_ids, sourceType.evaluates rfl actualTypes store,
    raw.preserves_type sourceType rfl actualTypes⟩

theorem exact_checked_paths_keep_arbitrary_continuations_without_executing_them
    (type : Core.Ty) (value : Core.Value) (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps 4 ⟨.eval oneCore [value], continuation, store⟩ ⟨.ret value, continuation, store⟩ ∧
    Core.Steps 4 (Core.State.initial oneCore [value] store) (Core.State.final value store) :=
  ⟨(counted value store).checked_toStepsWithContinuation (elaborated type).complete rfl continuation,
    (counted value store).checked_toSteps (elaborated type).complete rfl⟩

theorem aligned_untyped_payloads_preserve_raw_core_meaning_but_not_the_declared_value_type
    (store finalStore : Core.Store) (value : Core.Value) :
    elaborateTypedLetReturnBody? (types .word) owner (inputs .word) one = some (oneCore, .word) ∧
    (TypedLetReturnBodyEvaluates owner table (environment (.bool true)) store one value finalStore ↔
      Core.Evaluates [.bool true] store oneCore value finalStore) ∧
    Core.Evaluates [.bool true] store oneCore (.bool true) store ∧ ¬ Core.ValueHasType (.bool true) .word :=
  ⟨(elaborated .word).complete, elaborateTypedLetReturnBody?_evaluates_iff (elaborated .word).complete rfl,
    (elaborateTypedLetReturnBody?_evaluates_iff (elaborated .word).complete rfl).mp (counted (.bool true) store).erase,
    by intro impossible; cases impossible⟩

theorem existing_typed_cells_and_captured_closures_are_neither_allocated_nor_invoked
    (location : Core.Location) (word : Core.Word) (store : Core.Store) (continuation : List Core.Frame) :
    Core.ValueHasType (.cellRef .word location) (.cell .word) ∧
    Core.ValueHasType (.closure .bool .word (.var 1) [.word word]) (.function .bool .word) ∧
    Core.Steps 4 ⟨.eval oneCore [.cellRef .word location], continuation, store⟩ ⟨.ret (.cellRef .word location), continuation, store⟩ ∧
    Core.Steps 4 ⟨.eval oneCore [.closure .bool .word (.var 1) [.word word]], continuation, store⟩
      ⟨.ret (.closure .bool .word (.var 1) [.word word]), continuation, store⟩ :=
  ⟨.cellRef, .closure (.cons .word .nil) (.var rfl),
    (counted (.cellRef .word location) store).checked_toStepsWithContinuation (elaborated (.cell .word)).complete rfl continuation,
    (counted (.closure .bool .word (.var 1) [.word word]) store).checked_toStepsWithContinuation
      (elaborated (.function .bool .word)).complete rfl continuation⟩

theorem a_safe_pending_frame_exhausts_but_an_incompatible_endpoint_faults_at_zero_fuel (store : Core.Store) :
    Core.runStateful 4 ⟨.eval oneCore [.bool true], [.unaryApply .boolNot], store⟩ =
      .outOfFuel ⟨.ret (.bool true), [.unaryApply .boolNot], store⟩ ∧
    Core.runStateful 0 ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ =
      .fault (.invalidUnaryOperand .wordNot (.bool true)) ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ ∧
    Core.runStateful 4 ⟨.eval oneCore [.bool true], [.unaryApply .wordNot], store⟩ =
      .fault (.invalidUnaryOperand .wordNot (.bool true)) ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ := ⟨rfl, rfl, rfl⟩

private def subtract (left right : String) : Syntax.Expr := ⟨span, .binary (ref left) ⟨span, .subtract⟩ (ref right)⟩
private def pairInputs : LocalTypeInputs := ⟨[⟨"left", id 0, .word⟩, ⟨"right", id 1, .word⟩], by decide⟩
private def pairEnv (left right : Core.Word) : Resolved.Environment := [(id 0, .word left), (id 1, .word right)]
private def unused : Syntax.Block := ⟨span, [binding "unused" (subtract "left" "right"), returned (subtract "right" "left")]⟩
private def unusedCore : Core.Expr := .letE (.binary .wordSub (.var 0) (.var 1)) (.binary .wordSub (.var 2) (.var 1))
private theorem unusedElab : TypedLetReturnBodyElaborates (types .word) owner pairInputs unused unusedCore .word :=
  .binding (.named .head) (by decide)
    (.subtract (.identifier .head) (.identifier (.tail (by decide) .head)))
    (.binary (.var .head) (.var (.tail (by decide) .head)))
    (.binary (.var .head) (.var (.tail (by decide) .head)))
    (.terminal (.single (.expression
      (.subtract (.identifier (.tail (by decide) (.tail (by decide) .head))) (.identifier (.tail (by decide) .head)))
      (.binary (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) .head)))
      (.binary (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) .head))))))
private theorem unusedCost (left right : Core.Word) (store : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner pairInputs.names (pairEnv left right) store unused (.word (right.sub left)) store 12 := by
  have lhs : LocalExpressionEvaluatesWithCost pairInputs.names (pairEnv left right) store (ref "left") (.word left) store 1 := .identifier .head .head
  have rhs : LocalExpressionEvaluatesWithCost pairInputs.names (pairEnv left right) store (ref "right") (.word right) store 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  have initial : LocalExpressionEvaluatesWithCost pairInputs.names (pairEnv left right) store
      (subtract "left" "right") (.word (left.sub right)) store 5 := .subtract lhs rhs
  apply TypedLetReturnBodyEvaluatesWithCost.binding (owner := owner) (name := ⟨span, "unused"⟩)
    (annotation := annotation) (tailCost := 5) initial
  change TypedLetReturnBodyEvaluatesWithCost owner (("unused", id 2) :: pairInputs.names)
    ((id 2, .word (left.sub right)) :: pairEnv left right) store ⟨span, [returned (subtract "right" "left")]⟩ (.word (right.sub left)) store 5
  have nextRight : LocalExpressionEvaluatesWithCost (("unused", id 2) :: pairInputs.names)
      ((id 2, .word (left.sub right)) :: pairEnv left right) store (ref "right") (.word right) store 1 :=
    .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
  have nextLeft : LocalExpressionEvaluatesWithCost (("unused", id 2) :: pairInputs.names)
      ((id 2, .word (left.sub right)) :: pairEnv left right) store (ref "left") (.word left) store 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  exact .terminal (.single (.expression (.subtract nextRight nextLeft)))

theorem unused_noncommutative_initializers_are_evaluated_in_old_scope_and_still_cost_five
    (left right : Core.Word) (store : Core.Store) (continuation : List Core.Frame) :
    elaborateTypedLetReturnBody? (types .word) owner pairInputs unused = some (unusedCore, .word) ∧
    TypedLetReturnBodyEvaluatesWithCost owner pairInputs.names (pairEnv left right) store unused (.word (right.sub left)) store 12 ∧
    Core.Steps 12 ⟨.eval unusedCore [.word left, .word right], continuation, store⟩
      ⟨.ret (.word (right.sub left)), continuation, store⟩ ∧
    ¬ TypedLetReturnBodyEvaluatesWithCost owner pairInputs.names (pairEnv left right) store unused (.word (right.sub left)) store 7 := by
  refine ⟨unusedElab.complete, unusedCost left right store,
    (unusedCost left right store).checked_toStepsWithContinuation unusedElab.complete rfl continuation, ?_⟩
  intro skipped
  have impossible := (skipped.deterministic (unusedCost left right store)).2.2
  cases impossible

private def badConditional : Syntax.Expr := ⟨span, .conditional (ref "seed") span (ref "seed") span (ref "missing")⟩
private def bad (inInitializer : Bool) : Syntax.Block := if inInitializer then
  ⟨span, [binding "x" badConditional, returned (ref "seed")]⟩ else
  ⟨span, [binding "x" (ref "seed"), ⟨span, .ifThen (ref "seed") ⟨span, [returned (ref "seed")]⟩
    (some ⟨span, [returned (ref "missing")]⟩)⟩]⟩
private theorem badCost (inInitializer : Bool) (store : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner table (environment (.bool true)) store (bad inInitializer) (.bool true) store 7 := by
  have seed : LocalExpressionEvaluatesWithCost table (environment (.bool true)) store (ref "seed") (.bool true) store 1 := .identifier .head .head
  have tailSeed : LocalExpressionEvaluatesWithCost (("x", id 1) :: table) ((id 1, .bool true) :: environment (.bool true))
      store (ref "seed") (.bool true) store 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  cases inInitializer
  · apply TypedLetReturnBodyEvaluatesWithCost.binding (owner := owner) (name := ⟨span, "x"⟩)
      (annotation := annotation) (tailCost := 4) seed
    exact .terminal (.ifTrue tailSeed (.single (.expression tailSeed)))
  · have initializer : LocalExpressionEvaluatesWithCost table (environment (.bool true)) store badConditional (.bool true) store 4 := .ifTrue seed seed
    apply TypedLetReturnBodyEvaluatesWithCost.binding (owner := owner) (name := ⟨span, "x"⟩)
      (annotation := annotation) (tailCost := 1) initializer
    exact .terminal (.single (.expression tailSeed))

theorem skipped_bad_initializer_subexpressions_and_terminal_arms_still_fail_whole_checking
    (inInitializer : Bool) (store : Core.Store) :
    TypedLetReturnBodyEvaluates owner table (environment (.bool true)) store (bad inInitializer) (.bool true) store ∧
    TypedLetReturnBodyEvaluatesWithCost owner table (environment (.bool true)) store (bad inInitializer) (.bool true) store 7 ∧
    elaborateTypedLetReturnBody? (types .bool) owner (inputs .bool) (bad inInitializer) = none := by
  refine ⟨(badCost inInitializer store).erase, badCost inInitializer store, ?_⟩
  cases inInitializer <;> simp [bad, badConditional, binding, returned, elaborateTypedLetReturnBody?, elaborateTerminalReturnTree?,
    elaborateReturnBody?, elaborateLocalExpression?, resolveLocalExpression?, ref, inputs, types, annotation,
    LocalTypeInputs.bindFresh, LocalTypeInputs.names, LocalTypeInputs.empty, LocalNameTable.lookup?]

theorem an_evaluated_missing_initializer_cannot_be_skipped_even_when_its_name_is_unused
    (store finalStore : Core.Store) (value : Core.Value) :
    ¬ TypedLetReturnBodyEvaluates owner table (environment (.bool true)) store
      ⟨span, [binding "x" (ref "missing"), returned (ref "seed")]⟩ value finalStore := by
  intro raw
  cases raw with
  | terminal tree => cases tree with | single leaf => cases leaf
  | binding initializer _ =>
      cases initializer with
      | identifier named _ =>
          have found := LocalNameTable.lookup?_iff.mpr named
          simp [table, LocalNameTable.lookup?] at found

theorem typed_values_cannot_replace_the_missing_identity_alignment (store : Core.Store) :
    let initial : LocalTypeInputs := ⟨[⟨"seed", id 0, .bool⟩, ⟨"other", id 9, .bool⟩], by decide⟩
    let swapped : Resolved.Environment := [(id 9, .bool false), (id 0, .bool true)]
    elaborateTypedLetReturnBody? (types .bool) owner initial one = some (oneCore, .bool) ∧
    swapped.ids ≠ initial.context.ids ∧ Core.EnvironmentHasTypes swapped.values initial.context.values ∧
    TypedLetReturnBodyEvaluates owner initial.names swapped store one (.bool true) store ∧
    Core.Evaluates swapped.values store oneCore (.bool false) store ∧ ¬ Core.Evaluates swapped.values store oneCore (.bool true) store := by
  intro initial swapped
  have exact : TypedLetReturnBodyElaborates (types .bool) owner initial one oneCore .bool :=
    .binding (.named .head) (by decide) (.identifier .head) (.var .head) (.var .head)
      (.terminal (.single (.expression (.identifier .head) (.var .head) (.var .head))))
  have wrong : Core.Evaluates swapped.values store oneCore (.bool false) store := .letE (.var rfl) (.var rfl)
  refine ⟨exact.complete, by decide, .cons .bool (.cons .bool .nil),
    chainRaw ["x"] "seed" initial.names swapped (.bool true) store (.identifier .head (.tail (by decide) .head)), wrong, ?_⟩
  intro impossible
  cases (Core.evaluation_deterministic impossible wrong).1

theorem original_raw_and_counted_tree_paths_embed_without_checking_or_extra_cost
    (names : LocalNameTable) (values : Resolved.Environment) (store finalStore : Core.Store) (body : Syntax.Block)
    (value : Core.Value) (cost : Nat) (raw : TerminalReturnTreeEvaluates names values store body value finalStore)
    (counted : TerminalReturnTreeEvaluatesWithCost names values store body value finalStore cost) :
    TypedLetReturnBodyEvaluates owner names values store body value finalStore ∧
    TypedLetReturnBodyEvaluatesWithCost owner names values store body value finalStore cost :=
  ⟨raw.typedLetReturnBody owner, counted.typedLetReturnBody owner⟩

end Tests.FrontendTypedLetReturnBodyEvaluation
end

section
-- leanmerge: from Solcore.Test.FrontendTypedLetReturnBodyOwnerProperties
/-! Owner-only covariance preserves fresh allocation and exact positional Core.
Static nominal inputs and actual runtime values remain separate boundaries. -/

set_option autoImplicit false

namespace Tests.FrontendTypedLetReturnBodyOwner

open Solcore Solcore.Frontend

private def owner (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetOwners", by decide⟩], by decide⟩⟩, index⟩
private def localId (declaration index : Nat) : Resolved.LocalId := ⟨owner declaration, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-owners.sol"⟩, 177, 8⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def binding (name : String) (value : Syntax.Expr) : Syntax.Statement :=
  ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some value)⟩
private def returned (value : Syntax.Expr) : Syntax.Statement := ⟨span, .returnStmt (some value)⟩
private def statements : List String → String → List Syntax.Statement
  | [], previous => [returned (ref previous)]
  | name :: rest, previous => binding name (ref previous) :: statements rest name
private def chain (names : List String) (previous : String) : Syntax.Block := ⟨span, statements names previous⟩
private def chainCore : Nat → Core.Expr
  | 0 => .var 0
  | count + 1 => .letE (.var 0) (chainCore count)
private def initial (type : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"seed", localId 0 7, type⟩, ⟨"side", localId 1 199, .word⟩, ⟨"old", localId 0 2, .bool⟩],
    by change [localId 0 7, localId 1 199, localId 0 2].Nodup; decide⟩
private def mapped (inputs : LocalTypeInputs) (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) := inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)
private theorem chainElaborated (names : List String) (previous : String) (type : Core.Ty)
    (inputs : LocalTypeInputs) (resolved : Resolved.Expr)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ inputs.names.map Prod.fst)
    (resolution : ResolvesLocalExpression inputs.names (ref previous) resolved)
    (lowered : Resolved.Lowers inputs.ids resolved (.var 0)) (typing : Resolved.HasType inputs.context resolved type) :
    TypedLetReturnBodyElaborates (types type) (owner 0) inputs (chain names previous) (chainCore names.length) type := by
  induction names generalizing previous inputs resolved with
  | nil =>
      simp only [chain, statements, List.length_nil, chainCore]
      exact .terminal (.single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing))
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      simp only [chain, statements, List.length_cons, chainCore]
      apply TypedLetReturnBodyElaborates.binding (name := ⟨span, name⟩) (annotation := annotation)
        (.named .head) (fresh name (by simp)) resolution lowered typing
      apply ih name (inputs.bindFresh (owner 0) name type) _ parts.2
      · intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
      · exact .identifier .head
      · exact .var .head
      · exact .var .head
private theorem seedChain (names : List String) (type : Core.Ty) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "old"]) :
    TypedLetReturnBodyElaborates (types type) (owner 0) (initial type) (chain names "seed") (chainCore names.length) type :=
  chainElaborated names "seed" type (initial type) _ distinct fresh (.identifier .head) (.var .head) (.var .head)
private def shift (id : Resolved.DeclarationId) : Resolved.DeclarationId := { id with declarationIndex := id.declarationIndex + 5 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl

theorem arbitrary_raw_scopes_and_value_free_extended_inputs_commute_with_owner_allocation
    (scope : List Resolved.LocalId) (inputs : LocalTypeInputs) (declaration : Resolved.DeclarationId)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) (name : String) (type : Core.Ty) :
    Resolved.freshLocalId (mapping declaration) (scope.map (ownerLocalIdMap mapping)) =
      ⟨mapping declaration, (Resolved.freshLocalId declaration scope).binderIndex⟩ ∧
    mapped (inputs.bindFresh declaration name type) mapping injective =
      (mapped inputs mapping injective).bindFresh (mapping declaration) name type :=
  ⟨Resolved.freshLocalId_map_owner mapping injective declaration scope, inputs.bindFresh_mapOwner declaration mapping injective name type⟩

theorem sparse_mixed_owners_and_repeated_raw_ids_do_not_replace_maximum_index_allocation_with_row_count
    (type : Core.Ty) :
    Resolved.freshLocalId (owner 0) [localId 0 7, localId 1 199, localId 0 2, localId 0 7] = localId 0 8 ∧
    Resolved.freshLocalId (shift (owner 0)) ([localId 0 7, localId 1 199, localId 0 2, localId 0 7].map (ownerLocalIdMap shift)) = localId 5 8 ∧
    (((mapped (initial type) shift shiftInjective).bindFresh (owner 5) "x" type).bindFresh (owner 5) "y" type).ids =
      [localId 5 9, localId 5 8, localId 5 7, localId 6 199, localId 5 2] :=
  ⟨rfl, Resolved.freshLocalId_map_owner shift shiftInjective (owner 0) _, rfl⟩

theorem arbitrary_length_independent_static_provenance_and_typing_keep_exact_core
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "old"])
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    TypedLetReturnBodyElaborates (types type) (mapping (owner 0)) (mapped (initial type) mapping injective)
      (chain names "seed") (chainCore names.length) type ∧
    TypedLetReturnBodyHasType (types type) (mapping (owner 0)) (mapped (initial type) mapping injective) (chain names "seed") type ∧
    elaborateTypedLetReturnBody? (types type) (mapping (owner 0)) (mapped (initial type) mapping injective) (chain names "seed") =
      some (chainCore names.length, type) :=
  ⟨(seedChain names type distinct fresh).mapOwner mapping injective, (seedChain names type distinct fresh).hasType.mapOwner mapping injective,
    (elaborateTypedLetReturnBody?_mapOwner mapping injective (types type) (owner 0) (initial type) _).trans (seedChain names type distinct fresh).complete⟩

theorem nonsurjective_owner_changes_preserve_nominal_provenance_without_supplying_an_inhabitant
    (names : List String) (nominal : Core.DataTypeId) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "old"]) :
    ¬ Function.Surjective shift ∧
    elaborateTypedLetReturnBody? (types (.namedData nominal)) (owner 5) (mapped (initial (.namedData nominal)) shift shiftInjective)
      (chain names "seed") = some (chainCore names.length, .namedData nominal) ∧ ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨?_, (arbitrary_length_independent_static_provenance_and_typing_keep_exact_core names _ distinct fresh shift shiftInjective).2.2, ?_⟩
  · intro onto
    obtain ⟨preimage, same⟩ := onto (owner 0)
    have indices := congrArg Resolved.DeclarationId.declarationIndex same
    change preimage.declarationIndex + 5 = 0 at indices
    omega
  · rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem row_order_spellings_types_and_indices_remain_fixed_while_actual_owners_change (type : Core.Ty) :
    (mapped (initial type) shift shiftInjective).ids = [localId 5 7, localId 6 199, localId 5 2] ∧
    (mapped (initial type) shift shiftInjective).names.map Prod.fst = ["seed", "side", "old"] ∧
    (mapped (initial type) shift shiftInjective).context.values = [type, .word, .bool] ∧
    (mapped (initial type) shift shiftInjective).ids.map (·.binderIndex) = (initial type).ids.map (·.binderIndex) ∧
    (mapped (initial type) shift shiftInjective).ids ≠ (initial type).ids := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro same
  have head := congrArg (fun ids => ids.head?.map (·.owner.declarationIndex)) same
  cases head

private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def inputs {type : Core.Ty} (actual : Actual type) (side : Core.Word) (old : Bool) : LocalInputs :=
  ⟨[⟨"seed", localId 0 7, type, actual.val, actual.property⟩, ⟨"side", localId 1 199, .word, .word side, .word⟩,
    ⟨"old", localId 0 2, .bool, .bool old, .bool⟩], by change [localId 0 7, localId 1 199, localId 0 2].Nodup; decide⟩
private def mappedValues (inputs : LocalInputs) (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) := inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)
theorem actual_typed_inputs_preserve_complete_checker_and_runner_options_at_every_fuel
    {type : Core.Ty} (actual : Actual type) (side : Core.Word) (old : Bool) (body : Syntax.Block) (fuel : Nat) (store : Core.Store)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    (mappedValues (inputs actual side old) mapping injective).checkTypedLetReturnBody? (types type) (mapping (owner 0)) body =
      (inputs actual side old).checkTypedLetReturnBody? (types type) (owner 0) body ∧
    (mappedValues (inputs actual side old) mapping injective).runTypedLetReturnBody? (types type) (mapping (owner 0)) fuel body store =
      (inputs actual side old).runTypedLetReturnBody? (types type) (owner 0) fuel body store :=
  ⟨(inputs actual side old).checkTypedLetReturnBody?_mapOwner mapping injective (types type) (owner 0) body,
    (inputs actual side old).runTypedLetReturnBody?_mapOwner mapping injective (types type) (owner 0) fuel body store⟩

private def subtract (left right : String) : Syntax.Expr := ⟨span, .binary (ref left) ⟨span, .subtract⟩ (ref right)⟩
private def ordered : Syntax.Block := ⟨span, [binding "x" (subtract "seed" "side"), binding "y" (ref "x"), returned (subtract "side" "x")]⟩
private def orderedTail : Core.Expr := .letE (.var 0) (.binary .wordSub (.var 3) (.var 1))
private def orderedCore : Core.Expr := .letE (.binary .wordSub (.var 0) (.var 1)) orderedTail
private theorem orderedElab : TypedLetReturnBodyElaborates (types .word) (owner 0) (initial .word) ordered orderedCore .word :=
  .binding (.named .head) (by decide)
    (.subtract (.identifier .head) (.identifier (.tail (by decide) .head)))
    (.binary (.var .head) (.var (.tail (by decide) .head))) (.binary (.var .head) (.var (.tail (by decide) .head)))
    (.binding (.named .head) (by decide) (.identifier .head) (.var .head) (.var .head)
      (.terminal (.single (.expression
        (.subtract (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.identifier (.tail (by decide) .head)))
        (.binary (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) .head)))
        (.binary (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) .head)))))))
private def checkpoint (seed side : Core.Word) (old : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret (.word seed), [.binaryRight .wordSub (.var 1) [.word seed, .word side, .bool old],
    .letBody orderedTail [.word seed, .word side, .bool old]], store⟩
private def tailCheckpoint (seed side : Core.Word) (old : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret (.word (seed.sub side)), [.letBody (.binary .wordSub (.var 3) (.var 1)) [.word (seed.sub side), .word seed, .word side, .bool old]], store⟩
private theorem exhausted (seed side : Core.Word) (old : Bool) (store : Core.Store) :
    (inputs ⟨.word seed, .word⟩ side old).runTypedLetReturnBody? (types .word) (owner 0) 3 ordered store = some (.word, .outOfFuel (checkpoint seed side old store)) :=
  LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨orderedCore, orderedElab.complete, rfl⟩

theorem exact_noncommutative_core_and_genuine_checkpoints_survive_nonsurjective_owner_changes
    (seed side : Core.Word) (old : Bool) (store : Core.Store) (additional : Nat) :
    (mappedValues (inputs ⟨.word seed, .word⟩ side old) shift shiftInjective).checkTypedLetReturnBody? (types .word) (owner 5) ordered = some (orderedCore, .word) ∧
    (mappedValues (inputs ⟨.word seed, .word⟩ side old) shift shiftInjective).runTypedLetReturnBody? (types .word) (owner 5) 3 ordered store =
      some (.word, .outOfFuel (checkpoint seed side old store)) ∧
    Core.runStateful 6 (checkpoint seed side old store) = .outOfFuel (tailCheckpoint seed side old store) ∧
    (mappedValues (inputs ⟨.word seed, .word⟩ side old) shift shiftInjective).runTypedLetReturnBody? (types .word) (owner 5) 9 ordered store =
      some (.word, .outOfFuel (tailCheckpoint seed side old store)) ∧
    Core.runStateful 6 (tailCheckpoint seed side old store) = .done (.word (side.sub (seed.sub side))) store ∧
    (mappedValues (inputs ⟨.word seed, .word⟩ side old) shift shiftInjective).runTypedLetReturnBody? (types .word) (owner 5) (3 + additional) ordered store =
      some (.word, Core.runStateful additional (checkpoint seed side old store)) ∧
    (mappedValues (inputs ⟨.word seed, .word⟩ side old) shift shiftInjective).runTypedLetReturnBody? (types .word) (owner 5) (9 + additional) ordered store =
      some (.word, Core.runStateful additional (tailCheckpoint seed side old store)) := by
  have relabeled := ((inputs ⟨.word seed, .word⟩ side old).runTypedLetReturnBody?_mapOwner shift shiftInjective (types .word) (owner 0) 3 ordered store).trans
    (exhausted seed side old store)
  have tailOriginal : (inputs ⟨.word seed, .word⟩ side old).runTypedLetReturnBody? (types .word) (owner 0) 9 ordered store =
      some (.word, .outOfFuel (tailCheckpoint seed side old store)) :=
    LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨orderedCore, orderedElab.complete, rfl⟩
  have tailRelabeled := ((inputs ⟨.word seed, .word⟩ side old).runTypedLetReturnBody?_mapOwner shift shiftInjective (types .word) (owner 0) 9 ordered store).trans tailOriginal
  exact ⟨((inputs ⟨.word seed, .word⟩ side old).checkTypedLetReturnBody?_mapOwner shift shiftInjective (types .word) (owner 0) ordered).trans orderedElab.complete,
    relabeled, rfl, tailRelabeled, rfl, LocalInputs.runTypedLetReturnBody?_resume relabeled additional,
    LocalInputs.runTypedLetReturnBody?_resume tailRelabeled additional⟩

private theorem oneMapped {type : Core.Ty} (actual : Actual type) (side : Core.Word) (old : Bool) (store : Core.Store) :
    (mappedValues (inputs actual side old) shift shiftInjective).runTypedLetReturnBody? (types type) (owner 5) 4 (chain ["x"] "seed") store =
      some (type, .done actual.val store) :=
  ((inputs actual side old).runTypedLetReturnBody?_mapOwner shift shiftInjective (types type) (owner 0) 4 _ store).trans
    (LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨chainCore 1, (seedChain ["x"] type (by decide) (by decide)).complete, rfl⟩)
theorem actual_cells_and_closures_keep_the_identical_store_bearing_completed_result
    (location : Core.Location) (word side : Core.Word) (old : Bool) (store : Core.Store) :
    (mappedValues (inputs (⟨.cellRef .word location, .cellRef⟩ : Actual (.cell .word)) side old) shift shiftInjective).runTypedLetReturnBody?
      (types (.cell .word)) (owner 5) 4 (chain ["x"] "seed") store = some (.cell .word, .done (.cellRef .word location) store) ∧
    (mappedValues (inputs (⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ : Actual (.function .bool .word)) side old)
      shift shiftInjective).runTypedLetReturnBody? (types (.function .bool .word)) (owner 5) 4 (chain ["x"] "seed") store =
      some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨oneMapped _ side old store, oneMapped _ side old store⟩

theorem unknown_annotation_failure_survives_owner_changes_without_an_inverse_map
    {type : Core.Ty} (actual : Actual type) (side : Core.Word) (old : Bool) (fuel : Nat) (store : Core.Store) :
    elaborateTypedLetReturnBody? [] (owner 5) (mapped (initial type) shift shiftInjective) (chain ["x"] "seed") = none ∧
    (mappedValues (inputs actual side old) shift shiftInjective).runTypedLetReturnBody? [] (owner 5) fuel (chain ["x"] "seed") store = none := by
  have rejected : elaborateTypedLetReturnBody? [] (owner 0) (initial type) (chain ["x"] "seed") = none := by
    simp [chain, statements, binding, elaborateTypedLetReturnBody?, interpretTypeName?, annotation, TypeNameTable.lookup?]
  exact ⟨(elaborateTypedLetReturnBody?_mapOwner shift shiftInjective [] (owner 0) (initial type) _).trans rejected,
    ((inputs actual side old).runTypedLetReturnBody?_mapOwner shift shiftInjective [] (owner 0) fuel _ store).trans
      (LocalInputs.runTypedLetReturnBody?_eq_none_iff.mpr rejected)⟩

private def collapse (_ : Resolved.DeclarationId) := owner 0
private def indexShift (id : Resolved.LocalId) : Resolved.LocalId := { id with binderIndex := id.binderIndex + 10 }
theorem owner_collapse_and_injective_index_shifts_do_not_commute_with_fresh_allocation :
    ¬ Function.Injective collapse ∧
    Resolved.freshLocalId (collapse (owner 0)) ([localId 1 199].map (ownerLocalIdMap collapse)) = localId 0 200 ∧
    ownerLocalIdMap collapse (Resolved.freshLocalId (owner 0) [localId 1 199]) = localId 0 0 ∧
    Resolved.freshLocalId (collapse (owner 0)) ([localId 1 199].map (ownerLocalIdMap collapse)) ≠
      ownerLocalIdMap collapse (Resolved.freshLocalId (owner 0) [localId 1 199]) ∧
    Function.Injective indexShift ∧
    Resolved.freshLocalId (owner 0) ([].map indexShift) ≠ indexShift (Resolved.freshLocalId (owner 0) []) := by
  refine ⟨?_, rfl, rfl, by decide, ?_, by decide⟩
  · intro injective
    have same := injective (a₁ := owner 0) (a₂ := owner 1) rfl
    cases same
  · intro left right same
    have owners := congrArg Resolved.LocalId.owner same
    have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
    cases left; cases right; cases owners; cases indices; rfl

end Tests.FrontendTypedLetReturnBodyOwner
end

section
-- leanmerge: from Solcore.Test.FrontendTypedLetReturnBodyProperties
/-! Independent, value-free let chains preserve original initializer scopes and
already shifted tails. Negative results describe only this restricted adapter. -/

set_option autoImplicit false

namespace Tests.FrontendTypedLetReturnBody

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TypedPrefix", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "typed-prefix.sol"⟩, 133, 11⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Payload"], .word), (["Word"], .word)]
private def inputs (type : Core.Ty) : LocalTypeInputs := LocalTypeInputs.empty.bindFresh owner "seed" type
private def returned (name : String) : Syntax.Statement := ⟨span, .returnStmt (some (ref name))⟩
private def binding (name previous : String) : Syntax.Statement :=
  ⟨span, .letDecl ⟨span, name⟩ (some (annotation "Payload")) (some (ref previous))⟩
private def statements : List String → String → List Syntax.Statement
  | [], previous => [returned previous]
  | name :: rest, previous => binding name previous :: statements rest name
private def chain (names : List String) (previous : String) : Syntax.Block := ⟨span, statements names previous⟩
private def core : Nat → Core.Expr
  | 0 => .var 0
  | count + 1 => .letE (.var 0) (core count)

private theorem chainElaborated (names : List String) (previous : String) (type : Core.Ty)
    (initial : LocalTypeInputs) (resolved : Resolved.Expr)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ initial.names.map Prod.fst)
    (resolution : ResolvesLocalExpression initial.names (ref previous) resolved)
    (lowered : Resolved.Lowers initial.ids resolved (.var 0))
    (typed : Resolved.HasType initial.context resolved type) :
    TypedLetReturnBodyElaborates (types type) owner initial (chain names previous) (core names.length) type := by
  induction names generalizing previous initial resolved with
  | nil =>
      simp only [chain, statements, List.length_nil, core]
      exact .terminal (.single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typed))
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      simp only [chain, statements, List.length_cons, core]
      apply TypedLetReturnBodyElaborates.binding (name := ⟨span, name⟩) (annotation := annotation "Payload")
        (.named .head) (fresh name (by simp)) resolution lowered typed
      apply ih name (initial.bindFresh owner name type) _ parts.2
      · intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
      · exact .identifier .head
      · exact .var .head
      · exact .var .head

private theorem seedChain (names : List String) (type : Core.Ty)
    (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnBodyElaborates (types type) owner (inputs type) (chain names "seed") (core names.length) type := by
  apply chainElaborated names "seed" type (inputs type) _ distinct
  · intro name member
    change name ∉ ["seed"]
    simpa only [List.mem_singleton] using (show name ≠ "seed" from fun same => fresh (same ▸ member))
  · exact .identifier .head
  · exact .var .head
  · exact .var .head

private theorem coreTyped (count : Nat) (type : Core.Ty) (context : Core.Context) (definitions : Core.DataEnvironment) :
    Core.HasType (type :: context) (core count) type definitions := by
  induction count generalizing context with
  | zero => exact .var rfl
  | succ count ih => exact .letE (.var rfl) (ih (type :: context))

theorem arbitrary_length_and_type_chains_have_independent_exact_source_provenance
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    (definitions : Core.DataEnvironment) :
    TypedLetReturnBodyElaborates (types type) owner (inputs type) (chain names "seed") (core names.length) type ∧
    TypedLetReturnBodyHasType (types type) owner (inputs type) (chain names "seed") type ∧
    elaborateTypedLetReturnBody? (types type) owner (inputs type) (chain names "seed") = some (core names.length, type) ∧
    Core.HasType [type] (core names.length) type definitions ∧ (chain names "seed").value.length = names.length + 1 := by
  have exact := seedChain names type distinct fresh
  refine ⟨exact, exact.hasType, elaborateTypedLetReturnBody?_iff.mpr exact, coreTyped _ type [] definitions, ?_⟩
  clear exact distinct fresh
  suffices ∀ previous, (statements names previous).length = names.length + 1 from this "seed"
  induction names with
  | nil => intro previous; rfl
  | cons name rest ih => intro previous; simp only [statements, List.length_cons, ih]

theorem nominal_let_chains_do_not_require_or_create_runtime_inhabitants
    (names : List String) (nominal : Core.DataTypeId) (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    elaborateTypedLetReturnBody? (types (.namedData nominal)) owner (inputs (.namedData nominal)) (chain names "seed") =
      some (core names.length, .namedData nominal) ∧ ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨(seedChain names _ distinct fresh).complete, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem all_static_interfaces_retain_the_exact_independently_derived_result
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    {candidate : Core.Expr} {candidateType : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? (types type) owner (inputs type) (chain names "seed") = some (candidate, candidateType)) :
    candidate = core names.length ∧ candidateType = type ∧ Core.HasType [type] candidate candidateType ∧
    TypedLetReturnBodyHasType (types type) owner (inputs type) (chain names "seed") candidateType ∧
    (∃ other, TypedLetReturnBodyElaborates (types type) owner (inputs type) (chain names "seed") other type) ∧
    (∃ other, elaborateTypedLetReturnBody? (types type) owner (inputs type) (chain names "seed") = some (other, type)) := by
  have exact := seedChain names type distinct fresh
  have reflected := elaborateTypedLetReturnBody?_elaborates accepted
  have same := reflected.result_unique exact
  refine ⟨same.1, same.2, elaborateTypedLetReturnBody?_core_hasType accepted,
    elaborateTypedLetReturnBody?_sound accepted, ?_, ?_⟩
  · exact (typedLetReturnBodyHasType_iff_elaborates_exact.mp exact.hasType)
  · exact (typedLetReturnBodyHasType_iff_elaborates.mp exact.hasType)

private def twoBody (blockSpan firstSpan secondSpan returnSpan : Syntax.SourceSpan) : Syntax.Block := ⟨blockSpan,
  [⟨firstSpan, (binding "x" "seed").value⟩, ⟨secondSpan, (binding "y" "x").value⟩, ⟨returnSpan, (returned "x").value⟩]⟩
private def twoCore : Core.Expr := .letE (.var 0) (.letE (.var 0) (.var 1))
private theorem twoTail (type : Core.Ty) (blockSpan secondSpan returnSpan : Syntax.SourceSpan) :
    TypedLetReturnBodyElaborates (types type) owner ((inputs type).bindFresh owner "x" type)
      ⟨blockSpan, [⟨secondSpan, (binding "y" "x").value⟩, ⟨returnSpan, (returned "x").value⟩]⟩
      (.letE (.var 0) (.var 1)) type :=
  .binding (.named .head) (by change "y" ∉ ["x", "seed"]; decide) (.identifier .head) (.var .head) (.var .head)
    (.terminal (.single (.expression (.identifier (.tail (by change "y" ≠ "x"; decide) .head))
      (.var (.tail (by change id 2 ≠ id 1; decide) .head)) (.var (.tail (by change id 2 ≠ id 1; decide) .head)))))
private theorem twoElaborated (type : Core.Ty) (blockSpan firstSpan secondSpan returnSpan : Syntax.SourceSpan) :
    TypedLetReturnBodyElaborates (types type) owner (inputs type)
      (twoBody blockSpan firstSpan secondSpan returnSpan) twoCore type :=
  .binding (.named .head) (by change "x" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
    (twoTail type blockSpan secondSpan returnSpan)

theorem written_let_spans_and_old_scope_positions_do_not_add_a_second_weakening
    (type : Core.Ty) (blockSpan firstSpan secondSpan returnSpan : Syntax.SourceSpan) :
    (twoBody blockSpan firstSpan secondSpan returnSpan).span = blockSpan ∧
    (twoBody blockSpan firstSpan secondSpan returnSpan).value.map (·.span) = [firstSpan, secondSpan, returnSpan] ∧
    elaborateTypedLetReturnBody? (types type) owner (inputs type) (twoBody blockSpan firstSpan secondSpan returnSpan) = some (twoCore, type) ∧
    elaborateLocalExpression? (inputs type).names (inputs type).context (ref "seed") = some (.var 0, type) ∧
    elaborateLocalExpression? ((inputs type).bindFresh owner "x" type).names
      ((inputs type).bindFresh owner "x" type).context (ref "x") = some (.var 0, type) :=
  ⟨rfl, rfl, (twoElaborated type blockSpan firstSpan secondSpan returnSpan).complete,
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head),
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)⟩

theorem successful_children_recover_the_original_initializer_and_exact_remaining_source (type : Core.Ty) :
    ∃ declaredType initializerCore tailCore,
      "x" ∉ (inputs type).names.map Prod.fst ∧ interpretTypeName? (types type) (annotation "Payload") = some declaredType ∧
      elaborateLocalExpression? (inputs type).names (inputs type).context (ref "seed") = some (initializerCore, declaredType) ∧
      elaborateTypedLetReturnBody? (types type) owner ((inputs type).bindFresh owner "x" declaredType)
        ⟨span, [binding "y" "x", returned "x"]⟩ = some (tailCore, type) ∧ twoCore = .letE initializerCore tailCore :=
  elaborateTypedLetReturnBody?_binding_children (twoElaborated type span span span span).complete

theorem a_same_typed_wrong_tail_does_not_supply_exact_source_provenance (type : Core.Ty) :
    Core.HasType [type] (.letE (.var 0) (.letE (.var 0) (.var 0))) type ∧
    ¬ TypedLetReturnBodyElaborates (types type) owner (inputs type) (twoBody span span span span)
      (.letE (.var 0) (.letE (.var 0) (.var 0))) type := by
  refine ⟨.letE (.var rfl) (.letE (.var rfl) (.var rfl)), ?_⟩
  intro wrong
  have same := (wrong.result_unique (twoElaborated type span span span span)).1
  cases same

private inductive Bad where
  | noAnnotation | noInitializer | unknownAnnotation | mismatchedInitializer | missingUnused | selfReference
  | forwardReference | existingName | duplicateName | invalidArm | branchPrefix | extraReturn | blockWrapper
private def badBody : Bad → Syntax.Block
  | .noAnnotation => ⟨span, [⟨span, .letDecl ⟨span, "x"⟩ none (some (ref "seed"))⟩, returned "seed"]⟩
  | .noInitializer => ⟨span, [⟨span, .letDecl ⟨span, "x"⟩ (some (annotation "Payload")) none⟩, returned "seed"]⟩
  | .unknownAnnotation => ⟨span, [⟨span, .letDecl ⟨span, "x"⟩ (some (annotation "Unknown")) (some (ref "seed"))⟩, returned "seed"]⟩
  | .mismatchedInitializer => ⟨span, [⟨span, .letDecl ⟨span, "x"⟩ (some (annotation "Word")) (some (ref "seed"))⟩, returned "seed"]⟩
  | .missingUnused => ⟨span, [binding "x" "missing", returned "seed"]⟩
  | .selfReference => ⟨span, [binding "x" "x", returned "seed"]⟩
  | .forwardReference => ⟨span, [binding "x" "y", binding "y" "seed", returned "seed"]⟩
  | .existingName => ⟨span, [binding "seed" "seed", returned "seed"]⟩
  | .duplicateName => ⟨span, [binding "x" "seed", binding "x" "seed", returned "seed"]⟩
  | .invalidArm => ⟨span, [binding "x" "seed", ⟨span, .ifThen (ref "seed") ⟨span, [returned "seed"]⟩ (some ⟨span, [returned "missing"]⟩)⟩]⟩
  | .branchPrefix => ⟨span, [⟨span, .ifThen (ref "seed") (chain ["x"] "seed") (some ⟨span, [returned "seed"]⟩)⟩]⟩
  | .extraReturn => ⟨span, [binding "x" "seed", returned "x", returned "seed"]⟩
  | .blockWrapper => ⟨span, [⟨span, .block (chain ["x"] "seed").value⟩]⟩

theorem omitted_parts_name_capture_unused_failures_and_outside_shapes_are_adapter_failures (bad : Bad) :
    elaborateTypedLetReturnBody? (types .bool) owner (inputs .bool) (badBody bad) = none ∧
    ¬ ∃ type, TypedLetReturnBodyHasType (types .bool) owner (inputs .bool) (badBody bad) type := by
  have rejected : elaborateTypedLetReturnBody? (types .bool) owner (inputs .bool) (badBody bad) = none := by
    have seedAccepted : elaborateLocalExpression? (inputs .bool).names (inputs .bool).context (ref "seed") = some (.var 0, .bool) :=
      elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
    cases bad <;> simp [badBody, chain, statements, binding, returned, elaborateTypedLetReturnBody?,
      elaborateTerminalReturnTree?, elaborateReturnBody?, elaborateLocalExpression?, resolveLocalExpression?,
      ref, inputs, types, annotation, interpretTypeName?, qualifiedTypeNameKey, TypeNameTable.lookup?,
      Syntax.NonemptyList.toList, LocalTypeInputs.bindFresh, LocalTypeInputs.names, LocalTypeInputs.empty, LocalNameTable.lookup?]
    intro initializerCore initializerType accepted same
    simp [elaborateLocalExpression?, resolveLocalExpression?, ref, inputs, LocalTypeInputs.bindFresh,
      LocalTypeInputs.names, LocalTypeInputs.empty, LocalNameTable.lookup?] at seedAccepted
    rw [seedAccepted] at accepted
    cases accepted
    cases same
  exact ⟨rejected, elaborateTypedLetReturnBody?_eq_none_iff.mp rejected⟩

private def parameter : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, "seed"⟩ (annotation "Payload")⟩
private def declaration : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "prefix"⟩, none, ⟨span, [parameter]⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation "Payload"]⟩⟩, none⟩, twoBody span span span span⟩⟩

theorem valid_header_and_parameter_compile_the_exact_prefix_while_the_tree_adapter_still_rejects (type : Core.Ty) :
    RuntimeFunctionHeader (types type) declaration.value.signature type ∧
    RuntimeParametersDeclare (types type) owner [parameter] (inputs type) ∧
    elaborateTypedLetReturnBody? (types type) owner (inputs type) declaration.value.body = some (twoCore, type) ∧
    elaborateTerminalReturnTree? (inputs type).names (inputs type).context declaration.value.body = none ∧
    compileRuntimeFunction? (types type) owner declaration = some ⟨inputs type, twoCore, type⟩ := by
  refine ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil,
    (twoElaborated type span span span span).complete,
    by simp [declaration, twoBody, binding, elaborateTerminalReturnTree?], ?_⟩
  have compiled : RuntimeFunctionCompiles (types type) owner declaration ⟨inputs type, twoCore, type⟩ :=
    ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
      .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil,
      (twoElaborated type span span span span).returnTree⟩
  exact compiled.complete

private def otherId : Resolved.LocalId := ⟨{ owner with declarationIndex := 1 }, 999⟩
private def sparse (type : Core.Ty) : LocalTypeInputs := ⟨
  [⟨"seed", id 7, type⟩, ⟨"old", id 2, type⟩, ⟨"other", otherId, .bool⟩],
  by change [id 7, id 2, otherId].Nodup; decide⟩

theorem sparse_same_owner_and_large_unrelated_ids_do_not_turn_freshness_into_row_count (type : Core.Ty) :
    (sparse type).ids.length = 3 ∧ Resolved.freshLocalId owner (sparse type).ids = id 8 ∧
    ((sparse type).bindFresh owner "x" type).ids = [id 8, id 7, id 2, otherId] ∧
    elaborateTypedLetReturnBody? (types type) owner (sparse type) (chain ["x"] "seed") =
      some (.letE (.var 0) (.var 0), type) := by
  refine ⟨rfl, by rfl, rfl, ?_⟩
  apply TypedLetReturnBodyElaborates.complete
  apply chainElaborated ["x"] "seed" type (sparse type) _ (by decide)
  · intro name member
    have same : name = "x" := List.mem_singleton.mp member
    subst name
    change "x" ∉ ["seed", "old", "other"]
    decide
  · exact .identifier .head
  · exact .var .head
  · exact .var .head

theorem existing_terminal_provenance_embeds_without_any_type_or_value_invention
    (initial : LocalTypeInputs) (table : TypeNameTable) (body : Syntax.Block) (result : Core.Ty) (expression : Core.Expr)
    (tree : TerminalReturnTreeElaborates initial.names initial.context body expression result) :
    TypedLetReturnBodyHasType table owner initial body result ∧
    TypedLetReturnBodyElaborates table owner initial body expression result ∧
    elaborateTypedLetReturnBody? table owner initial body = some (expression, result) :=
  ⟨tree.hasType.typedLetReturnBody table owner, tree.typedLetReturnBody table owner,
    tree.typedLetReturnBody_complete table owner⟩

theorem old_return_and_conditional_shapes_keep_the_entire_optional_result
    (table : TypeNameTable) (initial : LocalTypeInputs) (value : Option Syntax.Expr)
    (condition : Syntax.Expr) (yes no : Syntax.Block) :
    elaborateTypedLetReturnBody? table owner initial ⟨span, [⟨span, .returnStmt value⟩]⟩ =
      elaborateReturnBody? initial.names initial.context ⟨span, [⟨span, .returnStmt value⟩]⟩ ∧
    elaborateTypedLetReturnBody? table owner initial ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩ =
      elaborateTerminalReturnTree? initial.names initial.context ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩ ∧
    elaborateTypedLetReturnBody? table owner initial
      ⟨span, [⟨span, .ifThen condition ⟨span, [⟨span, .returnStmt value⟩]⟩ (some ⟨span, [⟨span, .returnStmt none⟩]⟩)⟩]⟩ =
      elaborateConditionalReturnBody? initial.names initial.context
        ⟨span, [⟨span, .ifThen condition ⟨span, [⟨span, .returnStmt value⟩]⟩ (some ⟨span, [⟨span, .returnStmt none⟩]⟩)⟩]⟩ :=
  ⟨elaborateTypedLetReturnBody?_single table owner initial value span span,
    elaborateTypedLetReturnBody?_conditional table owner initial condition yes no span span,
    elaborateTypedLetReturnBody?_conditional_singletons table owner initial condition value none span span span span span span⟩

end Tests.FrontendTypedLetReturnBody
end

section
-- leanmerge: from Solcore.Test.FrontendTypedLetReturnBodyTypeExtensionProperties
/-! First-match meaning extension keeps fixed inputs and exact source results.
Repairing an unknown annotation is different from changing an existing meaning. -/

set_option autoImplicit false

namespace Tests.FrontendTypedLetReturnBodyTypeExtension

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetTypeTables", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-type-tables.sol"⟩, 191, 10⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def binding (annotation : Syntax.TypeExpr) (name : String) (value : Syntax.Expr) : Syntax.Statement :=
  ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some value)⟩
private def returned (value : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some value)⟩]⟩
private def statements (annotation : Syntax.TypeExpr) : List String → String → List Syntax.Statement
  | [], previous => (returned (ref previous)).value
  | name :: rest, previous => binding annotation name (ref previous) :: statements annotation rest name
private def chain (annotation : Syntax.TypeExpr) (names : List String) (previous : String) : Syntax.Block := ⟨span, statements annotation names previous⟩
private def chainCore : Nat → Core.Expr
  | 0 => .var 0
  | count + 1 => .letE (.var 0) (chainCore count)
private def initial (type : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"seed", id 0, type⟩, ⟨"side", id 1, .word⟩, ⟨"c", id 2, .bool⟩], by change [id 0, id 1, id 2].Nodup; decide⟩
private theorem chainElaborated (names : List String) (previous : String) (type : Core.Ty)
    (table : TypeNameTable) (annotation : Syntax.TypeExpr) (meaning : TypeNameDenotes table annotation type)
    (inputs : LocalTypeInputs) (resolved : Resolved.Expr) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ inputs.names.map Prod.fst)
    (resolution : ResolvesLocalExpression inputs.names (ref previous) resolved)
    (lowered : Resolved.Lowers inputs.ids resolved (.var 0)) (typing : Resolved.HasType inputs.context resolved type) :
    TypedLetReturnBodyElaborates table owner inputs (chain annotation names previous) (chainCore names.length) type := by
  induction names generalizing previous inputs resolved with
  | nil =>
      simp only [chain, statements, returned, List.length_nil, chainCore]
      exact .terminal (.single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing))
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      simp only [chain, statements, List.length_cons, chainCore]
      apply TypedLetReturnBodyElaborates.binding (name := ⟨span, name⟩) meaning (fresh name (by simp)) resolution lowered typing
      apply ih name (inputs.bindFresh owner name type) _ parts.2
      · intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
      · exact .identifier .head
      · exact .var .head
      · exact .var .head
private theorem seedChain (names : List String) (type : Core.Ty) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "c"]) :
    TypedLetReturnBodyElaborates (types type) owner (initial type) (chain (named "Payload") names "seed") (chainCore names.length) type :=
  chainElaborated names "seed" type (types type) (named "Payload") (.named .head) (initial type) _ distinct fresh
    (.identifier .head) (.var .head) (.var .head)
private theorem oneElab (type : Core.Ty) (table : TypeNameTable) (annotation : Syntax.TypeExpr)
    (meaning : TypeNameDenotes table annotation type) :
    TypedLetReturnBodyElaborates table owner (initial type) (chain annotation ["x"] "seed") (chainCore 1) type :=
  chainElaborated ["x"] "seed" type table annotation meaning (initial type) _ (by decide)
    (by change ∀ name ∈ ["x"], name ∉ ["seed", "side", "c"]; decide) (.identifier .head) (.var .head) (.var .head)

theorem arbitrary_length_independent_static_provenance_retains_the_exact_core_and_type
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "c"])
    (next : TypeNameTable) (extension : TypeNameTable.Extends (types type) next) :
    TypedLetReturnBodyElaborates next owner (initial type) (chain (named "Payload") names "seed") (chainCore names.length) type ∧
    TypedLetReturnBodyHasType next owner (initial type) (chain (named "Payload") names "seed") type ∧
    elaborateTypedLetReturnBody? next owner (initial type) (chain (named "Payload") names "seed") = some (chainCore names.length, type) :=
  ⟨(seedChain names type distinct fresh).extend_types extension, (seedChain names type distinct fresh).hasType.extend_types extension,
    elaborateTypedLetReturnBody?_some_of_extends extension (seedChain names type distinct fresh).complete⟩

theorem nominal_static_chains_extend_without_creating_runtime_inhabitants
    (names : List String) (nominal : Core.DataTypeId) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "c"]) (extras : TypeNameTable) :
    elaborateTypedLetReturnBody? (types (.namedData nominal) ++ extras) owner (initial (.namedData nominal))
      (chain (named "Payload") names "seed") = some (chainCore names.length, .namedData nominal) ∧ ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨(arbitrary_length_independent_static_provenance_retains_the_exact_core_and_type names _ distinct fresh _ (TypeNameTable.Extends.append_right _ extras)).2.2, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private def hidden (type later : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Payload"], later)]
private theorem hiddenExtends (type first second : Core.Ty) : TypeNameTable.Extends (hidden type first) (hidden type second) := by
  intro key result found
  cases found with
  | head => exact .head
  | tail different rest =>
      cases rest with
      | head => exact False.elim (different rfl)
      | tail _ absent => cases absent
private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def inputs {type : Core.Ty} (actual : Actual type) (side : Core.Word) (choice : Bool) : LocalInputs :=
  ⟨[⟨"seed", id 0, type, actual.val, actual.property⟩, ⟨"side", id 1, .word, .word side, .word⟩,
    ⟨"c", id 2, .bool, .bool choice, .bool⟩], by change [id 0, id 1, id 2].Nodup; decide⟩

theorem different_hidden_duplicates_preserve_complete_static_and_actual_options
    {type : Core.Ty} (actual : Actual type) (side : Core.Word) (choice : Bool) (body : Syntax.Block) (fuel : Nat) (store : Core.Store) :
    hidden type .word ≠ hidden type .bool ∧
    elaborateTypedLetReturnBody? (hidden type .word) owner (initial type) body = elaborateTypedLetReturnBody? (hidden type .bool) owner (initial type) body ∧
    (inputs actual side choice).checkTypedLetReturnBody? (hidden type .word) owner body = (inputs actual side choice).checkTypedLetReturnBody? (hidden type .bool) owner body ∧
    (inputs actual side choice).runTypedLetReturnBody? (hidden type .word) owner fuel body store =
      (inputs actual side choice).runTypedLetReturnBody? (hidden type .bool) owner fuel body store := by
  refine ⟨?_, elaborateTypedLetReturnBody?_eq_of_mutual_extends (hiddenExtends type .word .bool) (hiddenExtends type .bool .word) owner _ body,
    (inputs actual side choice).checkTypedLetReturnBody?_eq_of_mutual_extends (hiddenExtends type .word .bool) (hiddenExtends type .bool .word) owner body,
    (inputs actual side choice).runTypedLetReturnBody?_eq_of_mutual_extends (hiddenExtends type .word .bool) (hiddenExtends type .bool .word) owner fuel body store⟩
  intro same
  have later := congrArg (fun table => table[1]?) same
  cases later

private def subtract : Syntax.Expr := ⟨span, .binary (ref "seed") ⟨span, .subtract⟩ (ref "side")⟩
private def terminal : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") (returned (ref "y"))
  (some (returned ⟨span, .unary ⟨span, .bitNot⟩ (ref "y")⟩))⟩]⟩
private def ordered : Syntax.Block := ⟨span, binding (named "Payload") "x" subtract :: binding (named "Payload") "y" (ref "x") :: terminal.value⟩
private def terminalCore : Core.Expr := .ifE (.var 4) (.var 0) (.unary .wordNot (.var 0))
private def core : Core.Expr := .letE (.binary .wordSub (.var 0) (.var 1)) (.letE (.var 0) terminalCore)
private theorem orderedElab : TypedLetReturnBodyElaborates (types .word) owner (initial .word) ordered core .word :=
  .binding (.named .head) (by decide)
    (.subtract (.identifier .head) (.identifier (.tail (by decide) .head)))
    (.binary (.var .head) (.var (.tail (by decide) .head))) (.binary (.var .head) (.var (.tail (by decide) .head)))
    (.binding (.named .head) (by decide) (.identifier .head) (.var .head) (.var .head)
      (.terminal (.conditional
        (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
        (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
        (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
        (.single (.expression (.identifier .head) (.var .head) (.var .head)))
        (.single (.expression (.bitNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head)))))))
private theorem runExact (seed side : Core.Word) (choice : Bool) (store : Core.Store) (fuel : Nat) (result : Core.StatefulRunResult)
    (ran : Core.runStateful fuel (Core.State.initial core [.word seed, .word side, .bool choice] store) = result) :
    (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnBody? (types .word) owner fuel ordered store = some (.word, result) :=
  LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨core, orderedElab.complete, ran⟩

theorem one_way_extension_preserves_the_exact_successful_pair_even_before_completion
    (seed side : Core.Word) (choice : Bool) (store : Core.Store) (fuel : Nat) (next : TypeNameTable) (extension : TypeNameTable.Extends (types .word) next) :
    (inputs ⟨.word seed, .word⟩ side choice).checkTypedLetReturnBody? next owner ordered = some (core, .word) ∧
    (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnBody? next owner fuel ordered store =
      some (.word, Core.runStateful fuel (Core.State.initial core [.word seed, .word side, .bool choice] store)) :=
  ⟨LocalInputs.checkTypedLetReturnBody?_some_of_extends (inputs := inputs ⟨.word seed, .word⟩ side choice) extension orderedElab.complete,
    LocalInputs.runTypedLetReturnBody?_some_of_extends extension (runExact seed side choice store fuel _ rfl)⟩

private def checkpoint (seed side : Core.Word) (choice : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (.var 0) (.unary .wordNot (.var 0))
    [.word (seed.sub side), .word (seed.sub side), .word seed, .word side, .bool choice]], store⟩
theorem mutually_extending_tables_keep_the_genuine_checkpoint_and_asymmetric_residual_result
    (seed side : Core.Word) (choice : Bool) (store : Core.Store) (additional : Nat) :
    (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnBody? (hidden .word .word) owner 12 ordered store = some (.word, .outOfFuel (checkpoint seed side choice store)) ∧
    (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnBody? (hidden .word .bool) owner 12 ordered store = some (.word, .outOfFuel (checkpoint seed side choice store)) ∧
    Core.runStateful (if choice then 2 else 4) (checkpoint seed side choice store) =
      .done (.word (if choice then seed.sub side else (seed.sub side).bitNot)) store ∧
    (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnBody? (hidden .word .bool) owner (12 + additional) ordered store =
      some (.word, Core.runStateful additional (checkpoint seed side choice store)) := by
  have original : (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnBody? (types .word) owner 12 ordered store =
      some (.word, .outOfFuel (checkpoint seed side choice store)) := runExact seed side choice store 12 _ (by cases choice <;> rfl)
  have left := LocalInputs.runTypedLetReturnBody?_some_of_extends (TypeNameTable.Extends.append_right (types .word) [(["Payload"], .word)]) original
  have right := ((inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnBody?_eq_of_mutual_extends
    (hiddenExtends .word .word .bool) (hiddenExtends .word .bool .word) owner 12 ordered store).symm.trans left
  exact ⟨left, right, by cases choice <;> rfl, LocalInputs.runTypedLetReturnBody?_resume right additional⟩

private theorem oneCompleted {type : Core.Ty} (actual : Actual type) (side : Core.Word) (choice : Bool) (store : Core.Store) :
    (inputs actual side choice).runTypedLetReturnBody? (types type) owner 4 (chain (named "Payload") ["x"] "seed") store = some (type, .done actual.val store) :=
  LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨chainCore 1, (oneElab type (types type) (named "Payload") (.named .head)).complete, rfl⟩
theorem opaque_actual_cells_and_closures_keep_their_exact_completed_pairs_under_extension
    (location : Core.Location) (word side : Core.Word) (choice : Bool) (store : Core.Store) (extras : TypeNameTable) :
    (inputs (⟨.cellRef .word location, .cellRef⟩ : Actual (.cell .word)) side choice).runTypedLetReturnBody? (types (.cell .word) ++ extras) owner 4
      (chain (named "Payload") ["x"] "seed") store = some (.cell .word, .done (.cellRef .word location) store) ∧
    (inputs (⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ : Actual (.function .bool .word)) side choice).runTypedLetReturnBody?
      (types (.function .bool .word) ++ extras) owner 4 (chain (named "Payload") ["x"] "seed") store =
        some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨LocalInputs.runTypedLetReturnBody?_some_of_extends (TypeNameTable.Extends.append_right _ extras) (oneCompleted _ side choice store),
    LocalInputs.runTypedLetReturnBody?_some_of_extends (TypeNameTable.Extends.append_right _ extras) (oneCompleted _ side choice store)⟩

theorem adding_an_unknown_alias_repairs_whole_acceptance_with_the_same_fixed_inputs
    {type : Core.Ty} (actual : Actual type) (side : Core.Word) (choice : Bool) (store : Core.Store) (fuel : Nat) :
    TypeNameTable.Extends (types type) ((["Alias"], type) :: types type) ∧
    (inputs actual side choice).runTypedLetReturnBody? (types type) owner fuel (chain (named "Alias") ["x"] "seed") store = none ∧
    (inputs actual side choice).runTypedLetReturnBody? ((["Alias"], type) :: types type) owner fuel (chain (named "Alias") ["x"] "seed") store =
      some (type, Core.runStateful fuel (Core.State.initial (chainCore 1) [actual.val, .word side, .bool choice] store)) ∧
    typedLetReturnBodyFuelBound (chain (named "Alias") ["x"] "seed") = 4 := by
  refine ⟨TypeNameTable.Extends.cons_fresh _ ["Alias"] type (by change ["Alias"] ∉ [["Payload"]]; decide), ?_,
    LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨chainCore 1, (oneElab type ((["Alias"], type) :: types type) (named "Alias") (.named .head)).complete, rfl⟩, ?_⟩
  · apply LocalInputs.runTypedLetReturnBody?_eq_none_iff.mpr
    simp [LocalInputs.checkTypedLetReturnBody?, chain, statements, binding, elaborateTypedLetReturnBody?, interpretTypeName?, named, types,
      qualifiedTypeNameKey, TypeNameTable.lookup?, Syntax.NonemptyList.toList]
  · simp [chain, statements, binding, returned, ref, typedLetReturnBodyFuelBound, terminalReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]

theorem retaining_every_old_row_does_not_make_a_changed_first_meaning_an_extension :
    (∀ row ∈ types .word, row ∈ ((["Payload"], Core.Ty.bool) :: types .word)) ∧
    ¬ TypeNameTable.Extends (types .word) ((["Payload"], .bool) :: types .word) ∧
    elaborateTypedLetReturnBody? (types .word) owner (initial .word) (chain (named "Payload") ["x"] "seed") = some (chainCore 1, .word) ∧
    elaborateTypedLetReturnBody? ((["Payload"], .bool) :: types .word) owner (initial .word) (chain (named "Payload") ["x"] "seed") = none := by
  refine ⟨fun row member => List.mem_cons_of_mem _ member, ?_, (oneElab .word (types .word) (named "Payload") (.named .head)).complete, ?_⟩
  · intro extension
    have conflict := (extension (.head : TypeNameTable.Lookup (types .word) ["Payload"] .word)).type_unique (.head : TypeNameTable.Lookup _ ["Payload"] .bool)
    cases conflict
  · have seedAccepted : elaborateLocalExpression? (initial .word).names (initial .word).context (ref "seed") = some (.var 0, .word) :=
      elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
    simp [chain, statements, binding, elaborateTypedLetReturnBody?, seedAccepted, interpretTypeName?, named, types,
      qualifiedTypeNameKey, TypeNameTable.lookup?, Syntax.NonemptyList.toList]

private def qualified : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Pkg"⟩, [⟨span, "Token"⟩]⟩⟩⟩ none⟩
theorem qualified_components_are_not_replaced_by_a_single_dotted_key (type : Core.Ty) :
    TypeNameTable.Extends [(["Pkg", "Token"], type)] [(["Pkg.Token"], .bool), (["Pkg", "Token"], type)] ∧
    elaborateTypedLetReturnBody? [(["Pkg.Token"], .bool), (["Pkg", "Token"], type)] owner (initial type) (chain qualified ["x"] "seed") = some (chainCore 1, type) ∧
    elaborateTypedLetReturnBody? [(["Pkg.Token"], type)] owner (initial type) (chain qualified ["x"] "seed") = none := by
  refine ⟨TypeNameTable.Extends.cons_fresh _ ["Pkg.Token"] .bool (by change ["Pkg.Token"] ∉ [["Pkg", "Token"]]; decide),
    (oneElab type _ qualified (.named (.tail (by decide) .head))).complete, ?_⟩
  simp [chain, statements, binding, elaborateTypedLetReturnBody?, interpretTypeName?, qualified, qualifiedTypeNameKey,
    TypeNameTable.lookup?, Syntax.NonemptyList.toList]

end Tests.FrontendTypedLetReturnBodyTypeExtension
end

section
-- leanmerge: from Solcore.Test.FrontendTypedLetRuntimeEntryProperties
/-! Independent arbitrary-length entry provenance and actual cost keep prefix
locals out of the parameter record and retain real pending let continuations. -/

set_option autoImplicit false

namespace Tests.FrontendTypedLetRuntimeEntry

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetEntry", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-entry.sol"⟩, 211, 11⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Flag"], .bool)]
private def binding (name previous : String) : Syntax.Statement :=
  ⟨span, .letDecl ⟨span, name⟩ (some (named "Payload")) (some (ref previous))⟩
private def statements : List String → String → List Syntax.Statement
  | [], previous => [⟨span, .returnStmt (some (ref previous))⟩]
  | name :: rest, previous => binding name previous :: statements rest name
private def chain (names : List String) (previous : String) : Syntax.Block := ⟨span, statements names previous⟩
private def core : Nat → Core.Expr
  | 0 => .var 0
  | count + 1 => .letE (.var 0) (core count)
private def parameter (name type : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (named type)⟩
private def parameters := [parameter "flag" "Flag", parameter "seed" "Payload"]
private def declaration (names : List String) : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "chain"⟩, none, ⟨span, parameters⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [named "Payload"]⟩⟩, none⟩, chain names "seed"⟩⟩
private def initial (type : Core.Ty) : LocalTypeInputs :=
  (LocalTypeInputs.empty.bindFresh owner "flag" .bool).bindFresh owner "seed" type
private def compiled (names : List String) (type : Core.Ty) : CompiledRuntimeFunction := ⟨initial type, core names.length, type⟩
private theorem chainElaborated (names : List String) (previous : String) (type : Core.Ty)
    (inputs : LocalTypeInputs) (resolved : Resolved.Expr) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ inputs.names.map Prod.fst)
    (resolution : ResolvesLocalExpression inputs.names (ref previous) resolved)
    (lowered : Resolved.Lowers inputs.ids resolved (.var 0)) (typing : Resolved.HasType inputs.context resolved type) :
    TypedLetReturnBodyElaborates (types type) owner inputs (chain names previous) (core names.length) type := by
  induction names generalizing previous inputs resolved with
  | nil =>
      simp only [chain, statements, List.length_nil, core]
      exact .terminal (.single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing))
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      simp only [chain, statements, binding, List.length_cons, core]
      apply TypedLetReturnBodyElaborates.binding (name := ⟨span, name⟩)
        (show TypeNameDenotes (types type) (named "Payload") type from .named .head)
        (fresh name (by simp)) resolution lowered typing
      apply ih name (inputs.bindFresh owner name type) _ parts.2
      · intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
      · exact .identifier .head
      · exact .var .head
      · exact .var .head
private theorem compilation (names : List String) (type : Core.Ty) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    RuntimeFunctionCompiles (types type) owner (declaration names) (compiled names type) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named (.tail (by decide) .head)) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named .head) (by change "seed" ∉ ["flag"]; decide) .nil),
    (chainElaborated names "seed" type (initial type) _ distinct fresh (.identifier .head) (.var .head) (.var .head)).returnTree⟩

theorem arbitrary_length_whole_entry_compilation_needs_no_runtime_values
    (names : List String) (type : Core.Ty) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) (definitions : Core.DataEnvironment) :
    RuntimeFunctionCompiles (types type) owner (declaration names) (compiled names type) ∧
    compileRuntimeFunction? (types type) owner (declaration names) = some (compiled names type) ∧
    (compiled names type).inputs.names.map Prod.fst = ["seed", "flag"] ∧
    (compiled names type).inputs.context.values = [type, .bool] ∧ Core.HasType [type, .bool] (core names.length) type definitions := by
  refine ⟨compilation names type distinct fresh, (compilation names type distinct fresh).complete, rfl, rfl, ?_⟩
  have typed (count : Nat) (tail : List Core.Ty) : Core.HasType (type :: tail) (core count) type definitions := by
    induction count generalizing tail with
    | zero => exact .var rfl
    | succ count ih => exact .letE (.var rfl) (ih _)
  exact typed names.length [.bool]

theorem nominal_entry_compilation_does_not_manufacture_an_actual_argument
    (names : List String) (nominal : Core.DataTypeId) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    compileRuntimeFunction? (types (.namedData nominal)) owner (declaration names) = some (compiled names (.namedData nominal)) ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData nominal := by
  refine ⟨(compilation names _ distinct fresh).complete, ?_⟩
  rintro ⟨⟨type, value, typed⟩, same⟩
  cases same
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def arguments {type : Core.Ty} (flag : Bool) (actual : Actual type) : List TypedRuntimeArgument :=
  [⟨.bool, .bool flag, .bool⟩, ⟨type, actual.val, actual.property⟩]
private def inputs {type : Core.Ty} (flag : Bool) (actual : Actual type) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "flag" .bool (.bool flag) .bool).bindFresh owner "seed" type actual.val actual.property
private def prepared {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type) : PreparedRuntimeFunction :=
  ⟨inputs flag actual, core names.length, type⟩
private theorem preparation {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    RuntimeFunctionPrepares (types type) owner (declaration names) (arguments flag actual) (prepared names flag actual) :=
  ⟨(compilation names type distinct fresh).header,
    .cons (.named (.tail (by decide) .head)) (by simp [LocalInputs.empty, LocalInputs.names])
      (.cons (.named .head) (by change "seed" ∉ ["flag"]; decide) .nil), (compilation names type distinct fresh).body⟩
private theorem chainCost (names : List String) (previous : String) (table : LocalNameTable)
    (environment : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost table environment store (ref previous) value store 1) :
    TypedLetReturnBodyEvaluatesWithCost owner table environment store (chain names previous) value store (3 * names.length + 1) := by
  induction names generalizing previous table environment with
  | nil => exact .terminal (.single (.expression head))
  | cons name rest ih =>
      have arithmetic : 1 + (3 * rest.length + 1) + 2 = 3 * (name :: rest).length + 1 := by simp; omega
      simpa only [arithmetic, chain, statements, binding] using
        TypedLetReturnBodyEvaluatesWithCost.binding (name := ⟨span, name⟩) (annotation := named "Payload")
          head (ih name _ _ (.identifier .head .head))
private theorem costed {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type) (store : Core.Store)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    RuntimeFunctionEvaluatesWithCost (types type) owner (declaration names) (arguments flag actual) store type actual.val store (3 * names.length + 1) :=
  .intro (preparation names flag actual distinct fresh)
    (chainCost names "seed" (inputs flag actual).names (inputs flag actual).environment actual.val store (.identifier .head .head)).returnTree
private theorem bound (names : List String) (previous : String) :
    typedLetReturnBodyFuelBound (chain names previous) = 3 * names.length + 1 := by
  induction names generalizing previous with
  | nil => simp [chain, statements, ref, typedLetReturnBodyFuelBound, terminalReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]
  | cons name rest ih =>
      simp only [chain, statements, binding, typedLetReturnBodyFuelBound, ref, localExpressionFuelBound, List.length_cons]
      have tail := ih name
      simp only [chain] at tail
      rw [tail]; omega

theorem actual_preparation_retains_only_original_parameters_and_exactly_one_value_reverse
    {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type) (fuel : Nat) (store : Core.Store)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    prepareRuntimeFunction? (types type) owner (declaration names) (arguments flag actual) = some (prepared names flag actual) ∧
    (prepared names flag actual).toCompiled = compiled names type ∧
    (prepared names flag actual).inputs.environment.values = [actual.val, .bool flag] ∧
    runRuntimeFunction? (types type) owner (declaration names) (arguments flag actual) fuel store =
      some (type, Core.runStateful fuel (Core.State.initial (core names.length) [actual.val, .bool flag] store)) :=
  ⟨(preparation names flag actual distinct fresh).complete, rfl, rfl,
    (compilation names type distinct fresh).run_eq (arguments flag actual) rfl fuel store⟩

theorem independent_whole_entry_cost_proves_all_fuel_thresholds_and_actual_core_safety
    {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type) (store : Core.Store) (fuel : Nat)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) (error : Core.MachineFault) (state : Core.State) :
    Core.Steps (3 * names.length + 1) (Core.State.initial (core names.length) [actual.val, .bool flag] store) (Core.State.final actual.val store) ∧
    (runRuntimeFunction? (types type) owner (declaration names) (arguments flag actual) fuel store = some (type, .done actual.val store) ↔ 3 * names.length + 1 ≤ fuel) ∧
    ((∃ checkpoint, runRuntimeFunction? (types type) owner (declaration names) (arguments flag actual) fuel store = some (type, .outOfFuel checkpoint)) ↔ fuel < 3 * names.length + 1) ∧
    Core.runStateful fuel (Core.State.initial (core names.length) [actual.val, .bool flag] store) ≠ .fault error state :=
  ⟨(costed names flag actual store distinct fresh).compiled_toSteps (compilation names type distinct fresh),
    (costed names flag actual store distinct fresh).run_done_iff, (costed names flag actual store distinct fresh).run_outOfFuel_iff,
    (compilation names type distinct fresh).compiled_never_faults (arguments flag actual) rfl fuel store error state⟩

private theorem recursiveBound (names : List String) (previous : String) :
    typedLetReturnTreeFuelBound (chain names previous) = 3 * names.length + 1 := by
  induction names generalizing previous with
  | nil => simp [chain, statements, ref, typedLetReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]
  | cons name rest ih =>
      simp only [chain, statements, binding, typedLetReturnTreeFuelBound, ref, localExpressionFuelBound, List.length_cons]
      have tail := ih name
      simp only [chain] at tail
      rw [tail]; omega
theorem all_three_entry_bounds_include_strict_prefix_work
    {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type) (store : Core.Store)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    3 * names.length + 1 ≤ typedLetReturnTreeFuelBound (declaration names).value.body ∧
    (∃ value, Core.ValueHasType value type ∧ runRuntimeFunction? (types type) owner (declaration names)
      (arguments flag actual) (3 * names.length + 1) store = some (type, .done value store)) ∧
    (∃ value, Core.ValueHasType value type ∧ runRuntimeFunction? (types type) owner (declaration names)
      (arguments flag actual) (3 * names.length + 1) store = some (type, .done value store) ∧
      Core.runStateful (3 * names.length + 1) (Core.State.initial (core names.length) [actual.val, .bool flag] store) = .done value store) := by
  have enough : typedLetReturnTreeFuelBound (declaration names).value.body ≤ 3 * names.length + 1 := Nat.le_of_eq (recursiveBound names "seed")
  exact ⟨(costed names flag actual store distinct fresh).cost_le_fuelBound,
    (preparation names flag actual distinct fresh).hasType.run_done_of_fuelBound store _ enough,
    (compilation names type distinct fresh).run_done_of_fuelBound (arguments flag actual) rfl store _ enough⟩

theorem the_old_tree_bound_does_not_pay_for_a_valid_initialized_prefix
    {type : Core.Ty} (flag : Bool) (actual : Actual type) (store : Core.Store) :
    terminalReturnTreeFuelBound (declaration ["x"]).value.body = 0 ∧
    typedLetReturnBodyFuelBound (declaration ["x"]).value.body = 4 ∧
    (∃ checkpoint, runRuntimeFunction? (types type) owner (declaration ["x"]) (arguments flag actual) 0 store = some (type, .outOfFuel checkpoint)) ∧
    runRuntimeFunction? (types type) owner (declaration ["x"]) (arguments flag actual) 4 store = some (type, .done actual.val store) :=
  ⟨by simp [declaration, chain, statements, binding, terminalReturnTreeFuelBound], bound ["x"] "seed",
    (costed ["x"] flag actual store (by decide) (by decide)).run_outOfFuel_iff.mpr (by decide),
    (costed ["x"] flag actual store (by decide) (by decide)).run_done_iff.mpr (by decide)⟩

private def checkpoint {type : Core.Ty} (second : Bool) (flag : Bool) (actual : Actual type) (store : Core.Store) : Core.State :=
  ⟨.ret actual.val, [.letBody (if second then .var 0 else core 1)
    (if second then [actual.val, actual.val, .bool flag] else [actual.val, .bool flag])], store⟩
private theorem exhausted {type : Core.Ty} (second : Bool) (flag : Bool) (actual : Actual type) (store : Core.Store) :
    runRuntimeFunction? (types type) owner (declaration ["x", "y"]) (arguments flag actual) (if second then 5 else 2) store =
      some (type, .outOfFuel (checkpoint second flag actual store)) := by
  rw [(compilation ["x", "y"] type (by decide) (by decide)).run_eq (arguments flag actual) rfl]
  cases second <;> rfl

theorem genuine_two_let_checkpoints_and_multiple_chunks_retain_the_actual_remainder
    {type : Core.Ty} (flag : Bool) (actual : Actual type) (store : Core.Store) (additional : Nat) :
    runRuntimeFunction? (types type) owner (declaration ["x", "y"]) (arguments flag actual) 2 store = some (type, .outOfFuel (checkpoint false flag actual store)) ∧
    Core.runStateful 3 (checkpoint false flag actual store) = .outOfFuel (checkpoint true flag actual store) ∧
    runRuntimeFunction? (types type) owner (declaration ["x", "y"]) (arguments flag actual) 5 store = some (type, .outOfFuel (checkpoint true flag actual store)) ∧
    Core.Steps 2 (checkpoint true flag actual store) (Core.State.final actual.val store) ∧
    runRuntimeFunction? (types type) owner (declaration ["x", "y"]) (arguments flag actual) (5 + additional) store =
      some (type, Core.runStateful additional (checkpoint true flag actual store)) :=
  ⟨exhausted false flag actual store, rfl, exhausted true flag actual store,
    ((costed ["x", "y"] flag actual store (by decide) (by decide)).residual_of_outOfFuel (exhausted true flag actual store)).2,
    runRuntimeFunction?_resume (exhausted true flag actual store) additional⟩

theorem owner_changes_keep_full_checkpoints_and_store_replay_keeps_its_own_store
    {type : Core.Ty} (flag : Bool) (actual : Actual type) (otherOwner : Resolved.DeclarationId)
    (first replacement : Core.Store) (fuel : Nat) :
    runRuntimeFunction? (types type) otherOwner (declaration ["x", "y"]) (arguments flag actual) 5 first = some (type, .outOfFuel (checkpoint true flag actual first)) ∧
    RuntimeFunctionEvaluatesWithCost (types type) owner (declaration ["x", "y"]) (arguments flag actual) replacement type actual.val replacement 7 ∧
    ((∃ state, runRuntimeFunction? (types type) owner (declaration ["x", "y"]) (arguments flag actual) fuel first = some (type, .outOfFuel state)) ↔
      ∃ state, runRuntimeFunction? (types type) owner (declaration ["x", "y"]) (arguments flag actual) fuel replacement = some (type, .outOfFuel state)) :=
  ⟨(runRuntimeFunction?_owner_eq (types type) otherOwner owner _ _ 5 first).trans (exhausted true flag actual first),
    (costed ["x", "y"] flag actual first (by decide) (by decide)).change_store replacement,
    runRuntimeFunction?_outOfFuel_store_iff (types type) owner _ _ fuel first replacement type⟩

theorem semantic_type_extension_preserves_the_complete_original_parameter_record
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"])
    (next : TypeNameTable) (extension : TypeNameTable.Extends (types type) next) :
    RuntimeFunctionCompiles next owner (declaration names) (compiled names type) ∧
    compileRuntimeFunction? next owner (declaration names) = some (compiled names type) :=
  ⟨(compilation names type distinct fresh).extend_types extension,
    compileRuntimeFunction?_some_of_extends extension (compilation names type distinct fresh).complete⟩

theorem same_typed_wrong_core_does_not_satisfy_whole_source_provenance (type : Core.Ty) :
    Core.HasType [type, .bool] (.var 0) type ∧
    ¬ RuntimeFunctionCompiles (types type) owner (declaration ["x"]) { compiled ["x"] type with core := .var 0 } := by
  refine ⟨.var rfl, ?_⟩
  intro forged
  have wrong := congrArg CompiledRuntimeFunction.core (forged.result_unique (compilation ["x"] type (by decide) (by decide)))
  cases wrong

theorem missing_or_wrong_ordered_arguments_are_not_prefix_local_inputs
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"])
    (supplied : List TypedRuntimeArgument) (mismatch : supplied.map (·.type) ≠ [.bool, type]) (fuel : Nat) (store : Core.Store) :
    compileRuntimeFunction? (types type) owner (declaration names) = some (compiled names type) ∧
    runRuntimeFunction? (types type) owner (declaration names) supplied fuel store = none := by
  refine ⟨(compilation names type distinct fresh).complete, ?_⟩
  rw [runRuntimeFunction?_factorization, (compilation names type distinct fresh).complete]
  simp only [bind, Option.bind_some, compiled, initial, Resolved.LocalScope.values, LocalTypeInputs.context,
    LocalTypeInputs.bindFresh, LocalTypeInputs.empty, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, mismatch, ↓reduceIte]

theorem actual_cells_and_captured_closures_cross_prefixes_without_allocation_or_invocation
    (location : Core.Location) (word : Core.Word) (store : Core.Store) :
    runRuntimeFunction? (types (.cell .word)) owner (declaration ["x", "y"])
      (arguments true ⟨.cellRef .word location, .cellRef⟩) 7 store = some (.cell .word, .done (.cellRef .word location) store) ∧
    runRuntimeFunction? (types (.function .bool .word)) owner (declaration ["x", "y"])
      (arguments false ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩) 7 store =
      some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨(costed ["x", "y"] true _ store (by decide) (by decide)).run_done_iff.mpr (by decide),
    (costed ["x", "y"] false _ store (by decide) (by decide)).run_done_iff.mpr (by decide)⟩

end Tests.FrontendTypedLetRuntimeEntry
end
