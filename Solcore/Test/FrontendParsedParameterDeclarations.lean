import Solcore.Syntax.Parser.Signature
import Solcore.Syntax.Parser.Term
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.LocalInputsTypeErasure
import Solcore.Frontend.RuntimeParameters
import Solcore.Frontend.LocalExpressionTyping

/-! Complete canonical parameter text is declared without runtime values.
Real supplied arguments are tested separately against the same static rows.
Signature tests exercise only their parameter lists, not whole declarations. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-parameter-declarations.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Declarations", by decide⟩], by decide⟩⟩, 2⟩
private def types : TypeNameTable :=
  [(["Bool"], .bool), (["Boolean"], .bool), (["Word"], .word), (["Word"], .bool),
    (["Pkg", "Flag"], .bool), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
    (["Pair"], .product .word .bool), (["Choice"], .sum .word .bool)]
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def wordArg : TypedRuntimeArgument := ⟨.word, .word Core.Word.zero, .word⟩
private def cellArg : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
private def closureArg : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩

private def rows (inputs : LocalTypeInputs) : List (String × Resolved.LocalId × Core.Ty) :=
  inputs.bindings.map fun row => (row.name, row.id, row.type)

private def checkDeclaration (parameters : List Syntax.FunctionParameter)
    (expectedTypes : List Core.Ty) : IO LocalTypeInputs := do
  let names ← parameters.mapM fun parameter => do
    let .typed none name _ := parameter.value
      | throw (IO.userError "expected runtime-only annotated parameter")
    pure name.value
  assertTrue (decide (names.length = expectedTypes.length)) "invalid expected type count"
  let some inputs := declareRuntimeParameters? types owner parameters
    | throw (IO.userError "type-only declaration failed without supplied values")
  let expected := (names.zip expectedTypes).zipIdx.map fun (entry, index) =>
    (entry.1, (⟨owner, index⟩ : Resolved.LocalId), entry.2)
  assertTrue (decide (rows inputs = expected.reverse)) "static spelling, identity, type, or order changed"
  assertTrue (decide (inputs.context.values = expectedTypes.reverse)) "wrong reversed type context"
  assertTrue (decide (inputs.ids = (List.range names.length).reverse.map
    fun index => (⟨owner, index⟩ : Resolved.LocalId))) "wrong static allocation sequence"
  return inputs

private def declare (content : String) (expectedTypes : List Core.Ty) : IO LocalTypeInputs := do
  let some parameters ← parsed? Syntax.Parser.functionParameters content
    | throw (IO.userError s!"{content}: expected complete parameters")
  checkDeclaration parameters.elements expectedTypes

private def checkExpression (inputs : LocalTypeInputs) (content : String)
    (expectedCore : Core.Expr) (expectedType : Core.Ty) : IO Unit := do
  let some source ← parsed? Syntax.Parser.expression content
    | throw (IO.userError s!"{content}: expected a complete expression")
  assertTrue (decide (elaborateLocalExpression? inputs.names inputs.context source =
    some (expectedCore, expectedType))) s!"{content}: wrong value-free checking result"

private def checkBinding (content : String) (expectedTypes : List Core.Ty)
    (arguments : List TypedRuntimeArgument) : IO Unit := do
  let some parameters ← parsed? Syntax.Parser.functionParameters content
    | throw (IO.userError s!"{content}: expected complete parameters")
  let declared ← checkDeclaration parameters.elements expectedTypes
  let some bound := bindRuntimeParameters? types owner parameters.elements arguments
    | throw (IO.userError s!"{content}: matching actual arguments did not bind")
  assertTrue (decide (rows bound.toTypeInputs = rows declared)) "erasure changed exact static rows"
  assertTrue (decide (bound.names = declared.names)) "erasure changed the name table"
  assertTrue (decide (bound.context = declared.context)) "erasure changed the typing context"
  assertTrue (decide (bound.environment.values = arguments.reverse.map (·.value)))
    "static preparation lost actual argument values or their order"

private def checkProductParameter : IO Unit := do
  let content := "(x: (Word, Bool))"
  let some parameters ← parsed? Syntax.Parser.functionParameters content
    | throw (IO.userError "original product parameter did not fully parse")
  match parametersAt : parameters.elements with
  | [⟨_, .typed none name annotation⟩] =>
      match annotationAt : annotation with
      | ⟨_, .tuple [left, right]⟩ =>
          if meanings : interpretTypeName? types left = some .word ∧ interpretTypeName? types right = some .bool then
            have meaning : StructuralTypeDenotes types annotation (.product .word .bool) := by
              rw [annotationAt]
              exact .pair (interpretTypeName?_sound meanings.1).structural (interpretTypeName?_sound meanings.2).structural
            have independent : RuntimeParametersDeclare types owner parameters.elements
                (LocalTypeInputs.empty.bindFresh owner name.value (.product .word .bool)) := by
              rw [parametersAt]; exact .cons meaning (by simp) .nil
            have _ := independent.complete
            let inputs ← checkDeclaration parameters.elements [.product .word .bool]
            assertTrue (decide (rows inputs = [("x", ⟨owner, 0⟩, .product .word .bool)])) "product parameter was flattened"
            checkExpression inputs "x" (.var 0) (.product .word .bool)
            checkBinding content [.product .word .bool]
              [⟨.product .word .bool, .pair wordArg.value (.bool true), .pair .word .bool⟩]
          else throw (IO.userError "independent original product leaves changed")
      | _ => throw (IO.userError "original structural annotation lost its two children")
  | _ => throw (IO.userError "original source no longer has exactly one parameter")

def frontendParsedParameterDeclarationTests : IO Unit := do
  checkProductParameter
  let empty ← declare "()" []
  assertTrue empty.bindings.isEmpty "empty declaration introduced a binding"
  let opaqueInputs ← declare "(x: Opaque)" [.namedData ⟨91⟩]
  checkExpression opaqueInputs "x" (.var 0) (.namedData ⟨91⟩)
  let composite ← declare "(pair: Pair, choice: Choice)"
    [.product .word .bool, .sum .word .bool]
  checkExpression composite "pair" (.var 1) (.product .word .bool)
  checkExpression composite "choice" (.var 0) (.sum .word .bool)
  let branching ← declare "(c: Pkg /* alias */ . Flag, t: Word, f: Word,)" [.bool, .word, .word]
  checkExpression branching "c ? ~t : f" (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word
  for left in [false, true] do
    for right in [false, true] do
      checkBinding "(left: Bool, right: Boolean)" [.bool, .bool] [boolArg left, boolArg right]
  checkBinding "()" [] []
  checkBinding "(c: Bool, w: Word, cell: Cell, fn: Fn)"
    [.bool, .word, .cell .word, .function .bool .bool] [boolArg true, wordArg, cellArg, closureArg]
  let some signature ← parsed? (Syntax.Parser.functionSignature .module)
      "function declared(x: Opaque, y: Word) returns (Opaque)"
    | throw (IO.userError "expected a complete signature")
  let signatureInputs ← checkDeclaration signature.parameters.elements [.namedData ⟨91⟩, .word]
  checkExpression signatureInputs "x" (.var 1) (.namedData ⟨91⟩)
  for (content, expected, arguments) in [
      ("(x: Bool)", [.bool], []), ("()", [], [boolArg false]),
      ("(x: Bool)", [.bool], [boolArg false, boolArg true]),
      ("(x: Bool, y: Word)", [.bool, .word], [wordArg, boolArg true]),
      ("(x: Opaque)", [.namedData ⟨91⟩], []),
      ("(x: Word)", [.word], [boolArg true])] do
    let some parameters ← parsed? Syntax.Parser.functionParameters content
      | throw (IO.userError s!"{content}: mismatch case should parse")
    let _ ← checkDeclaration parameters.elements expected
    assertTrue (bindRuntimeParameters? types owner parameters.elements arguments).isNone
      s!"{content}: static success bypassed runtime arity or ordered type matching"
  for content in ["(x: Bool, x: Bool)", "(x: Bool, y: Word, x: Word)",
      "(x: Unknown)", "(x: bool)", "(x: Bool<Word>)", "(x: @Bool)",
      "(x: mapping(Word => Bool))", "(x: function(Word) returns (Bool))",
      "(comptime x: Bool)"] do
    let some parameters ← parsed? Syntax.Parser.functionParameters content
      | throw (IO.userError s!"{content}: adapter rejection case should parse")
    assertTrue (declareRuntimeParameters? types owner parameters.elements).isNone
      s!"{content}: unsupported static parameter profile was accepted"
  for content in ["", "(x)", "(x:)", "(x: Bool", "(x: Bool) trailing", "(x: comptime<Bool>)"] do
    assertTrue (← parsed? Syntax.Parser.functionParameters content).isNone
      s!"{content}: accepted malformed, diagnosed, or incompletely consumed parameters"

end Tests
