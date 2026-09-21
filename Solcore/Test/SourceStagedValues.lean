import Solcore

/-!
Executable regressions for the bounded Core-representable staged-value
evaluator introduced by ADR-0358.

The tests enter through concrete source specializations so that the evaluator
consumes the exact ADR-0357 side table associated with each checked function.
-/

set_option autoImplicit false

namespace Tests.SourceStagedValues

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceStageAnalysis Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def fixtureSource : String := String.intercalate "\n" [
  "function stagedUnit() returns (comptime<()>) { return; }",
  "function stagedBool(comptime value: Word, comptime flag: Bool) returns (comptime<Bool>) {",
  "  return !(value < 10) || flag;",
  "}",
  "function stagedWord(comptime value: Word) returns (comptime<Word>) {",
  "  let alias: Word = (value);",
  "  let alias: Word = alias + 1;",
  "  return ~alias;",
  "}",
  "function stagedProduct(comptime flag: Bool, comptime value: Word) returns (comptime<(Word, Bool, ())>) {",
  "  let alias: Word = (value);",
  "  let alias: Word = alias + 1;",
  "  return flag ? (alias, !flag, ()) : (9, false || flag, ());",
  "}",
  "function stagedProductInput(comptime value: (Word, Bool)) returns (comptime<(Word, Bool)>) {",
  "  return value;",
  "}",
  "function stagedStatements(comptime flag: Bool, comptime value: Word) returns (comptime<Word>) {",
  "  {",
  "    if (flag) {",
  "      return value + 2;",
  "    } else {",
  "      return value * 3;",
  "    }",
  "  }",
  "}",
  "function eagerProduct() returns (comptime<(Word, Bool, ())>) {",
  "  return true ? (1, true, ()) : (2, false, ());",
  "}",
  "function runtimeValue(value: Word) returns (Word) { return value; }",
  "function producer(value: Word) returns (Word) { return value; }",
  "function deferredValue() returns (Word) { return producer(1); }",
  "function markedConstant() returns (comptime<Word>) { return 7; }",
  "function unsupportedCall() returns (Word) { return markedConstant(); }"
]

private def checkedProgram : IO CheckedProgram := do
  match checkProgram (workspace fixtureSource) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"staged-value fixture failed checking: {reprStr errors}")

private def checkedNamed (program : CheckedProgram) (name : String) :
    IO (ProgramFunctionSignature × CheckedFunction) := do
  let signatures := program.signatures.functions.filter fun signature =>
    signature.name == name
  let signature ← match signatures with
    | [signature] => pure signature
    | _ => throw (IO.userError
        s!"expected one signature named `{name}`, found {signatures.length}")
  let functions := program.functions.filter fun function =>
    function.declaration == signature.id
  match functions with
  | [function] => pure (signature, function)
  | _ => throw (IO.userError
      s!"expected one checked body named `{name}`, found {functions.length}")

private def specializedNamed (program : CheckedProgram) (name : String) :
    IO SourceSpecialization.SpecializedFunction := do
  let (signature, function) ← checkedNamed program name
  unless signature.scheme.parameters.isEmpty do
    throw (IO.userError
      s!"staged-value fixture `{name}` unexpectedly remained generic")
  match SourceSpecialization.specializeFunction signature function [] with
  | .ok specialized => pure specialized
  | .error error => throw (IO.userError
      s!"{name}: specialization failed: {reprStr error}")

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def evaluateFunctionOrThrow (label : String)
    (specialized : SourceSpecialization.SpecializedFunction)
    (arguments : List SourceStagedValue.Value) :
    IO SourceStagedValue.Value := do
  match SourceCoreElaboration.evaluateStagedValueFunction specialized arguments with
  | .ok value => pure value
  | .error error => throw (IO.userError
      s!"{label}: staged-value evaluation failed: {reprStr error}")

private def returnedExpression
    (specialized : SourceSpecialization.SpecializedFunction) :
    IO ExpressionId :=
  match specialized.function.typedBody.roots with
  | [.statement statement] =>
      match specialized.function.typedBody.lookupStatement? statement with
      | some { form := .returnStmt (some expression), .. } => pure expression
      | _ => throw (IO.userError
          "staged-value fixture root is not a valued return")
  | roots => throw (IO.userError
      s!"staged-value fixture retained {roots.length} roots")

private def expectExpressionError (label : String)
    (specialized : SourceSpecialization.SpecializedFunction)
    (analysis : SourceStageAnalysis.Analysis) (expression : ExpressionId)
    (reason : SourceCoreElaboration.ErrorReason) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedValue analysis
      specialized.function.solvedRequirements specialized.function.typedBody
      expression with
  | .ok evaluated => throw (IO.userError
      s!"{label}: invalid expression evaluated to {reprStr evaluated}")
  | .error error =>
      assertTrue (decide (error.site = .occurrence expression.occurrence ∧
          error.reason = reason))
        s!"{label}: expected {reprStr reason}, found {reprStr error}"

private def assertRequirementFreeOperators
    (specialized : SourceSpecialization.SpecializedFunction) : IO Unit := do
  let operators := specialized.function.typedBody.nodes.filterMap fun
    | .expression node =>
        match node.form with
        | .unary ..
        | .binary .. => some node
        | _ => none
    | .statement _ => none
  assertTrue (!operators.isEmpty)
    "operator fixture retained no unary or binary nodes"
  assertTrue (operators.all fun node =>
      node.requirements.isEmpty && node.coercions.isEmpty)
    "staged builtin operator unexpectedly retained requirements or coercions"

private def testValueDomainAndExpressions (program : CheckedProgram) : IO Unit := do
  let unit ← specializedNamed program "stagedUnit"
  assertTrue unit.function.returnComptime
    "Unit function lost its marked-result contract"
  let unitValue ← evaluateFunctionOrThrow "staged Unit" unit []
  assertTrue (unitValue == .unit)
    s!"staged Unit returned {reprStr unitValue}"

  let bool ← specializedNamed program "stagedBool"
  assertTrue bool.function.returnComptime
    "Bool function lost its marked-result contract"
  assertRequirementFreeOperators bool
  let falseValue ← evaluateFunctionOrThrow "staged Bool false" bool
    [.word (word 7), .bool false]
  let trueValue ← evaluateFunctionOrThrow "staged Bool true" bool
    [.word (word 12), .bool false]
  assertTrue (falseValue == .bool false && trueValue == .bool true)
    "staged comparison, logical negation, or logical disjunction changed"

  let stagedWord ← specializedNamed program "stagedWord"
  assertTrue stagedWord.function.returnComptime
    "Word function lost its marked-result contract"
  assertRequirementFreeOperators stagedWord
  let wordValue ← evaluateFunctionOrThrow "staged Word" stagedWord
    [.word (word 3)]
  assertTrue (wordValue == .word (word 4).bitNot)
    "grouped alias, stable-ID shadowing, addition, or complement changed"

  let product ← specializedNamed program "stagedProduct"
  assertTrue product.function.returnComptime
    "product function lost its marked-result contract"
  assertRequirementFreeOperators product
  let thenValue ← evaluateFunctionOrThrow "staged product true" product
    [.bool true, .word (word 3)]
  let elseValue ← evaluateFunctionOrThrow "staged product false" product
    [.bool false, .word (word 3)]
  let expectedThen := SourceStagedValue.Value.product (.word (word 4))
    (.product (.bool false) .unit)
  let expectedElse := SourceStagedValue.Value.product (.word (word 9))
    (.product (.bool false) .unit)
  assertTrue (thenValue == expectedThen && elseValue == expectedElse)
    "three-element tuple association, expression conditional, or aliases changed"
  assertTrue (SourceStagedValue.sourceType thenValue =
      .product .word (.product .bool .unit) &&
      SourceStagedValue.toCore thenValue =
        .pair (.word (word 4)) (.pair (.bool false) .unit))
    "staged product lost its exact source type or Core projection"

  let productInput ← specializedNamed program "stagedProductInput"
  let supplied := SourceStagedValue.Value.product (.word (word 8)) (.bool true)
  let returned ← evaluateFunctionOrThrow "staged product input" productInput
    [supplied]
  assertTrue (returned == supplied)
    "product input did not retain its exact structural staged value"

private def testStatementEvaluation (program : CheckedProgram) : IO Unit := do
  let specialized ← specializedNamed program "stagedStatements"
  assertRequirementFreeOperators specialized
  let thenValue ← evaluateFunctionOrThrow "staged statement true" specialized
    [.bool true, .word (word 4)]
  let elseValue ← evaluateFunctionOrThrow "staged statement false" specialized
    [.bool false, .word (word 4)]
  assertTrue (thenValue == .word (word 6) && elseValue == .word (word 12))
    "terminal block/if or eager branch selection changed"

private def testEagerRequirementAccounting (program : CheckedProgram) : IO Unit := do
  let specialized ← specializedNamed program "eagerProduct"
  let expression ← returnedExpression specialized
  let evaluated ← match SourceCoreElaboration.evaluateStagedValue
      specialized.stageAnalysis specialized.function.solvedRequirements
      specialized.function.typedBody expression with
    | .ok evaluated => pure evaluated
    | .error error => throw (IO.userError
        s!"eager product expression failed: {reprStr error}")
  let expectedRequirements :=
    specialized.function.solvedRequirements.map fun requirement => requirement.id
  let expectedValue := SourceStagedValue.Value.product (.word (word 1))
    (.product (.bool true) .unit)
  assertTrue (expectedRequirements.length == 2 &&
      evaluated.value == expectedValue &&
      evaluated.consumedRequirements == expectedRequirements)
    "unselected tuple branch was not eagerly evaluated in ledger order"
  let functionValue ← evaluateFunctionOrThrow "eager product function"
    specialized []
  assertTrue (functionValue == expectedValue)
    "function-level exact ledger reconciliation changed the selected value"

private def testStageBoundaries (program : CheckedProgram) : IO Unit := do
  let runtime ← specializedNamed program "runtimeValue"
  let runtimeExpression ← returnedExpression runtime
  expectExpressionError "runtime stage" runtime runtime.stageAnalysis
    runtimeExpression .stagedValueExpressionRuntime

  let deferred ← specializedNamed program "deferredValue"
  let deferredExpression ← returnedExpression deferred
  expectExpressionError "deferred stage" deferred deferred.stageAnalysis
    deferredExpression .stagedValueExpressionDeferred

  let eager ← specializedNamed program "eagerProduct"
  let eagerExpression ← returnedExpression eager
  let missing : SourceStageAnalysis.Analysis := {
    eager.stageAnalysis with
    expressions := eager.stageAnalysis.expressions.filter fun entry =>
      entry.expression != eagerExpression
  }
  expectExpressionError "missing stage" eager missing eagerExpression
    .stagedValueExpressionStageMissing

  let unsupported ← specializedNamed program "unsupportedCall"
  let call ← returnedExpression unsupported
  expectExpressionError "unsupported staged call" unsupported
    unsupported.stageAnalysis call (.unsupportedExpression .call)

private def testArgumentBoundaries (program : CheckedProgram) : IO Unit := do
  let specialized ← specializedNamed program "stagedWord"
  match SourceCoreElaboration.evaluateStagedValueFunction specialized [] with
  | .error error =>
      assertTrue (decide (error.site = .declaration specialized.declaration ∧
          error.reason = .stagedValueArgumentArityMismatch 1 0))
        s!"wrong staged-value arity error: {reprStr error}"
  | .ok value => throw (IO.userError
      s!"missing staged argument produced {reprStr value}")
  let input ← match specialized.function.typedBody.inputs with
    | [input] => pure input
    | inputs => throw (IO.userError
        s!"stagedWord retained {inputs.length} inputs")
  match SourceCoreElaboration.evaluateStagedValueFunction specialized
      [.bool true] with
  | .error error =>
      assertTrue (decide (error.site = .binder input.id ∧
          error.reason = .stagedValueTypeMismatch .word .bool))
        s!"wrong staged-value argument type error: {reprStr error}"
  | .ok value => throw (IO.userError
      s!"wrong staged argument type produced {reprStr value}")

/-- Exercise the ADR-0358 standalone staged-value and function evaluators over
checked, concretely specialized source. -/
def testSourceStagedValues : IO Unit := do
  let program ← checkedProgram
  testValueDomainAndExpressions program
  testStatementEvaluation program
  testEagerRequirementAccounting program
  testStageBoundaries program
  testArgumentBoundaries program

end Tests.SourceStagedValues
