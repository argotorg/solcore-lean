import Solcore.Frontend.SourceCoreElaboration
import Solcore.Core.Machine

/-! End-to-end and malformed-carrier regressions for the first typed-source to
Semantic Core elaboration profile. -/

set_option autoImplicit false

namespace Tests.SourceCoreElaboration

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok checked => pure checked
  | .error errors =>
      throw (IO.userError s!"source-to-Core fixture failed checking: {reprStr errors}")

private def checkedNamed (program : CheckedProgram) (name : String) :
    IO CheckedFunction :=
  match program.functions.find? fun function =>
      match program.environment.declaration? function.declaration with
      | some declaration => declaration.name == some name
      | none => false with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def word (value : Nat) : Core.Word :=
  ⟨value % Core.wordModulus, Nat.mod_lt _ (by simp [Core.wordModulus])⟩

private def rootIds (function : CheckedFunction) :
    IO (StatementId × ExpressionId) :=
  match function.typedBody.roots with
  | [.statement statement] =>
      match function.typedBody.lookupStatement? statement with
      | some { form := .returnStmt (some expression), .. } =>
          pure (statement, expression)
      | _ => throw (IO.userError "fixture root is not a valued return")
  | _ => throw (IO.userError "fixture does not have one statement root")

private def changeExpression (source : TypedSource) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : TypedSource := {
  source with
  nodes := source.nodes.map fun
    | .expression node =>
        if node.id = id then .expression { change node with id }
        else .expression node
    | .statement node => .statement node
}

private def changeStatement (source : TypedSource) (id : StatementId)
    (change : StatementNode → StatementNode) : TypedSource := {
  source with
  nodes := source.nodes.map fun
    | .expression node => .expression node
    | .statement node =>
        if node.id = id then .statement { change node with id }
        else .statement node
}

private def withExpression (function : CheckedFunction) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : CheckedFunction := {
  function with typedBody := changeExpression function.typedBody id change
}

private def expectError (label : String) (function : CheckedFunction)
    (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.elaborateFunction function with
  | .ok _ => throw (IO.userError s!"{label}: malformed typed source lowered")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong elaboration error {reprStr error}"

private def testEndToEnd : IO CheckedFunction := do
  let program ← checkedProgram (String.intercalate "\n" [
    "function lower(flag: Bool, x: Word) returns (Word, Bool) {",
    "  return (((flag ? ((x + 1) * 2) : ~x), !(x < 10) || false));",
    "}",
    "function empty() { return; }"
  ])
  let function ← checkedNamed program "lower"
  let lowered ← match SourceCoreElaboration.elaborateFunction function with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"checked builtin function did not lower: {reprStr error}")
  assertTrue (decide (lowered.inputs.values = [.bool, .word] ∧
      lowered.returnType = .product .word .bool ∧
      Core.infer? lowered.inputs.values lowered.core = some lowered.returnType))
    "open Core context or independently inferred return type changed"
  assertTrue (decide (Core.runStateful 100
      (.initial lowered.core [.bool true, .word (word 3)]) =
        .done (.pair (.word (word 8)) (.bool false)) []))
    "lowered open Core expression did not execute to the source result"
  let empty ← checkedNamed program "empty"
  match SourceCoreElaboration.elaborateFunction empty with
  | .ok lowered =>
      assertTrue (decide (lowered.returnType = .unit ∧ lowered.core = .unit))
        "empty return did not lower to Core Unit"
  | .error error => throw (IO.userError
      s!"empty return did not lower: {reprStr error}")
  pure function

private def testStatementLowering : IO Unit := do
  let program ← checkedProgram (String.intercalate "\n" [
    "function statements(flag: Bool, x: Word) returns (Word) {",
    "  {",
    "    let base: Word = x + 1;",
    "    let base: Word = base * 2;",
    "    if (flag) {",
    "      return base + 10;",
    "    } else {",
    "      return x + 20;",
    "    }",
    "  }",
    "}"
  ])
  let function ← checkedNamed program "statements"
  let lowered ← match SourceCoreElaboration.elaborateFunction function with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"checked statement body did not lower: {reprStr error}")
  assertTrue (decide (lowered.inputs.values = [.bool, .word] ∧
      lowered.returnType = .word ∧
      Core.infer? lowered.inputs.values lowered.core = some .word))
    "statement lowering changed its open Core context or result type"
  assertTrue (decide (Core.runStateful 200
      (.initial lowered.core [.bool true, .word (word 3)]) =
        .done (.word (word 18)) []))
    "true tail-if branch lost initialized lets, shadowing, or input lookup"
  assertTrue (decide (Core.runStateful 200
      (.initial lowered.core [.bool false, .word (word 3)]) =
        .done (.word (word 23)) []))
    "false tail-if branch lost its outer input reference"

private def testUninitializedLetRejected : IO Unit := do
  let program ← checkedProgram (String.intercalate "\n" [
    "function uninitialized(x: Word) returns (Word) {",
    "  let pending: Word;",
    "  return pending;",
    "}"
  ])
  let function ← checkedNamed program "uninitialized"
  let statement ← match function.typedBody.roots with
    | .statement statement :: _ => pure statement
    | _ => throw (IO.userError
        "uninitialized-let fixture lost its first statement root")
  expectError "uninitialized let" function
    (.occurrence statement.occurrence)
    fun reason => reason matches .uninitializedLet

private def testRequirementsAndCoercions (function : CheckedFunction) : IO Unit := do
  let (_, expression) ← rootIds function
  let requirement : RequirementId := ⟨37⟩
  let required := withExpression function expression fun node => {
    node with requirements := [requirement]
  }
  expectError "requirement" required (.occurrence expression.occurrence)
    fun reason => match reason with
      | .requirementsPresent [id] => id == requirement
      | _ => false
  let coerced := withExpression function expression fun node => {
    node with
    requirements := [requirement]
    coercions := [{ requirement, source := .word, target := .bool }]
  }
  expectError "coercion" coerced (.occurrence expression.occurrence)
    fun reason => match reason with
      | .coercionsPresent [_] => true
      | _ => false

private def testUnsupportedExpressions (function : CheckedFunction) : IO Unit := do
  let (_, expression) ← rootIds function
  let cases : List
      (String × ExpressionForm × SourceCoreElaboration.UnsupportedExpression) := [
    ("call", .call expression [] .indirect, .call),
    ("lambda", .lambda [] .word [], .lambda),
    ("proxy", .proxy .word, .proxy),
    ("index", .index expression expression, .index)
  ]
  for (label, form, expected) in cases do
    let changed := withExpression function expression fun node => {
      node with form
    }
    expectError label changed (.occurrence expression.occurrence)
      fun reason => match reason with
        | .unsupportedExpression actual => actual == expected
        | _ => false

private def testBrokenEdges (function : CheckedFunction) : IO Unit := do
  let (statement, _) ← rootIds function
  let missingOccurrence : OccurrenceId := {
    owner := function.declaration
    index := function.typedBody.nodes.length + 100
  }
  let missing : ExpressionId := ⟨missingOccurrence⟩
  let missingFunction : CheckedFunction := {
    function with
    typedBody := changeStatement function.typedBody statement fun node => {
      node with form := .returnStmt (some missing)
    }
  }
  expectError "missing child" missingFunction (.occurrence missingOccurrence)
    fun reason => reason matches .missingNode
  let wrongCategory : ExpressionId := ⟨statement.occurrence⟩
  let wrongFunction : CheckedFunction := {
    function with
    typedBody := changeStatement function.typedBody statement fun node => {
      node with form := .returnStmt (some wrongCategory)
    }
  }
  expectError "wrong child category" wrongFunction
    (.occurrence statement.occurrence)
    fun reason => reason matches .expectedExpressionNode

private def testUnsupportedTypesAndDuplicateInputs
    (function : CheckedFunction) : IO Unit := do
  let input ← match function.typedBody.inputs with
    | input :: _ => pure input
    | [] => throw (IO.userError "lowering fixture lost its inputs")
  let variants : List (String × TypeSystem.Ty ×
      (SourceCoreElaboration.ErrorReason → Bool)) := [
    ("flexible variable", .variable ⟨91⟩, fun reason =>
      reason matches .flexibleTypeVariable _),
    ("rigid parameter", .parameter ⟨function.declaration, 7⟩, fun reason =>
      reason matches .rigidTypeParameter _),
    ("nominal", .constructor (.declaration function.declaration), fun reason =>
      reason matches .nominalType _)
  ]
  for (label, type, accepts) in variants do
    let changedInput := { input with scheme := .mono type }
    let changed : CheckedFunction := {
      function with typedBody := {
        function.typedBody with
        inputs := changedInput :: function.typedBody.inputs.tail
      }
    }
    expectError label changed (.binder input.id) accepts
  let duplicate : CheckedFunction := {
    function with typedBody := {
      function.typedBody with
      inputs := input :: function.typedBody.inputs
    }
  }
  expectError "duplicate input" duplicate (.binder input.id)
    fun reason => reason matches .duplicateInput _

private def testTypeMismatchAndUnconsumedRequirement
    (function : CheckedFunction) : IO Unit := do
  let (_, expression) ← rootIds function
  let mismatched := withExpression function expression fun node => {
    node with type := .bool
  }
  expectError "typed root mismatch" mismatched (.occurrence expression.occurrence)
    fun reason => reason matches .typedNodeTypeMismatch _ _
  let predicate : ProgramPredicate := {
    trait := function.declaration
    subject := .word
    arguments := []
  }
  let unconsumed : CheckedFunction := {
    function with
    solvedRequirements := [{
      id := ⟨73⟩
      predicate
      evidence := .assumption predicate
    }]
  }
  expectError "unconsumed requirement" unconsumed
    (.declaration function.declaration)
    fun reason => match reason with
      | .unconsumedRequirements [⟨73⟩] => true
      | _ => false

private def testOverflowLiteral : IO Unit := do
  let program ← checkedProgram
    "function overflow() returns (Word) { return 115792089237316195423570985008687907853269984665640564039457584007913129639936; }"
  let function ← checkedNamed program "overflow"
  let (_, expression) ← rootIds function
  expectError "overflow literal" function (.occurrence expression.occurrence)
    fun reason => reason matches .invalidWordLiteral _

/-- Exercise the complete first source-to-Core lowering profile and every
staged boundary that must reject explicitly. -/
def testSourceCoreElaboration : IO Unit := do
  let function ← testEndToEnd
  testStatementLowering
  testUninitializedLetRejected
  testRequirementsAndCoercions function
  testUnsupportedExpressions function
  testBrokenEdges function
  testUnsupportedTypesAndDuplicateInputs function
  testTypeMismatchAndUnconsumedRequirement function
  testOverflowLiteral

end Tests.SourceCoreElaboration
