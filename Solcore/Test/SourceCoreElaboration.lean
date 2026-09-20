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
    coercions := [{
      requirement
      source := .word
      target := node.type
    }]
  }
  expectError "coercion" coerced (.occurrence expression.occurrence)
    fun reason => match reason with
      | .coercionsPresent [_] => true
      | _ => false

private def requiredWordBinaryPolicy (consumed : List RequirementId) :
    SourceCoreElaboration.RequiredBinaryElaborator
      SourceCoreElaboration.Error :=
  fun _ _ _ _ _ => pure {
    leftType := .word
    rightType := .word
    consumedRequirements := consumed
    build := fun left right => pure (.binary .wordAdd left right)
  }

private def requiredWordUnaryPolicy (consumed : List RequirementId) :
    SourceCoreElaboration.RequiredUnaryElaborator
      SourceCoreElaboration.Error :=
  fun _ _ _ _ => pure {
    operandType := .word
    consumedRequirements := consumed
    build := fun operand => pure (.unary .wordNot operand)
  }

private def solvedWordRequirement (declaration : Resolved.DeclarationId)
    (requirement : RequirementId) : SolvedRequirement :=
  let predicate : ProgramPredicate := {
    trait := declaration
    subject := .word
    arguments := []
  }
  {
    id := requirement
    predicate
    evidence := .assumption predicate
  }

private def executableCoercionPolicy :
    SourceCoreElaboration.CoercionElaborator
      SourceCoreElaboration.Error :=
  fun _ node step =>
    match step.source, step.target with
    | .constructor (.builtin .word), .constructor (.builtin .bool) =>
        pure {
          sourceType := .word
          targetType := .bool
          consumedRequirements := [step.requirement]
          build := fun value => pure
            (.unary .boolNot (.binary .wordEq value (.word (word 0))))
        }
    | .constructor (.builtin .bool), .constructor (.builtin .word) =>
        pure {
          sourceType := .bool
          targetType := .word
          consumedRequirements := [step.requirement]
          build := fun value => pure
            (.ifE value (.word (word 1)) (.word (word 0)))
        }
    | _, _ => throw {
        site := .occurrence node.id.occurrence
        reason := .unsupportedType step.source
      }

private def constantCoercionPolicy (sourceType targetType : Core.Ty)
    (consumed : List RequirementId) :
    SourceCoreElaboration.CoercionElaborator
      SourceCoreElaboration.Error :=
  fun _ _ _ => pure {
    sourceType
    targetType
    consumedRequirements := consumed
    build := fun value => pure value
  }

private def expectCoercionPolicyError (label : String)
    (function : CheckedFunction) (expression : ExpressionId)
    (policy : SourceCoreElaboration.CoercionElaborator
      SourceCoreElaboration.Error)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.lowerFunctionBodyWithAllPolicies id
      SourceCoreElaboration.rejectCalls
      SourceCoreElaboration.rejectRequiredBinaries policy function with
  | .ok _ => throw (IO.userError s!"{label}: malformed coercion path lowered")
  | .error error =>
      assertTrue (decide (error.site = .occurrence expression.occurrence) &&
          accept error.reason)
        s!"{label}: wrong coercion error {reprStr error}"

private def testRequiredBinaryPolicy : IO Unit := do
  let program ← checkedProgram
    "function required(x: Word) returns (Word) { return x + 1; }"
  let function ← checkedNamed program "required"
  let (_, expression) ← rootIds function
  let requirement : RequirementId := ⟨101⟩
  let leftover : RequirementId := ⟨102⟩
  let predicate : ProgramPredicate := {
    trait := function.declaration
    subject := .word
    arguments := []
  }
  let required : CheckedFunction := {
    function with
    solvedRequirements := [{
      id := requirement
      predicate
      evidence := .assumption predicate
    }]
    typedBody := changeExpression function.typedBody expression fun node => {
      node with requirements := [requirement]
    }
  }
  expectError "required binary default policy" required
    (.occurrence expression.occurrence)
    fun reason => match reason with
      | .requirementsPresent [actual] => actual == requirement
      | _ => false
  let draft ← match SourceCoreElaboration.lowerFunctionBodyWithPolicies id
      SourceCoreElaboration.rejectCalls
      (requiredWordBinaryPolicy [requirement]) required with
    | .ok draft => pure draft
    | .error error => throw (IO.userError
        s!"required binary policy did not lower: {reprStr error}")
  let lowered ← match draft.finalize with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"required binary policy did not finalize: {reprStr error}")
  assertTrue (decide (Core.runStateful 100
      (.initial lowered.core [.word (word 4)]) =
        .done (.word (word 5)) []))
    "required binary policy changed child order or runtime meaning"
  match SourceCoreElaboration.lowerFunctionBodyWithPolicies id
      SourceCoreElaboration.rejectCalls (requiredWordBinaryPolicy [])
      required with
  | .ok _ => throw (IO.userError
      "required binary policy accepted mismatched requirement identities")
  | .error error =>
      assertTrue (decide (error.site = .occurrence expression.occurrence) &&
          match error.reason with
          | .binaryRequirementsMismatch [expected] [] =>
              expected == requirement
          | _ => false)
        s!"required binary mismatch reported the wrong error: {reprStr error}"
  let withLeftover : CheckedFunction := {
    required with
    solvedRequirements := required.solvedRequirements ++ [{
      id := leftover
      predicate
      evidence := .assumption predicate
    }]
  }
  let leftoverDraft ← match
      SourceCoreElaboration.lowerFunctionBodyWithPolicies id
        SourceCoreElaboration.rejectCalls
        (requiredWordBinaryPolicy [requirement]) withLeftover with
    | .ok draft => pure draft
    | .error error => throw (IO.userError
        s!"required binary leftover failed before finalization: {reprStr error}")
  match leftoverDraft.finalize with
  | .ok _ => throw (IO.userError
      "required binary policy silently discarded an unconsumed requirement")
  | .error error =>
      assertTrue (decide (error.site = .declaration function.declaration) &&
          match error.reason with
          | .unconsumedRequirements [actual] => actual == leftover
          | _ => false)
        s!"required binary leftover reported the wrong error: {reprStr error}"

private def testRequiredUnaryPolicy : IO Unit := do
  let program ← checkedProgram
    "function required(x: Word) returns (Word) { return ~x; }"
  let function ← checkedNamed program "required"
  let (_, expression) ← rootIds function
  let requirement : RequirementId := ⟨111⟩
  let predicate : ProgramPredicate := {
    trait := function.declaration
    subject := .word
    arguments := []
  }
  let required : CheckedFunction := {
    function with
    solvedRequirements := [{
      id := requirement
      predicate
      evidence := .assumption predicate
    }]
    typedBody := changeExpression function.typedBody expression fun node => {
      node with requirements := [requirement]
    }
  }
  expectError "required unary default policy" required
    (.occurrence expression.occurrence)
    fun reason => match reason with
      | .requirementsPresent [actual] => actual == requirement
      | _ => false
  match SourceCoreElaboration.lowerFunctionBodyWithAllPolicies id
      SourceCoreElaboration.rejectCalls
      SourceCoreElaboration.rejectRequiredBinaries
      SourceCoreElaboration.rejectCoercions required with
  | .ok _ => throw (IO.userError
      "required unary crossed the compatibility policy boundary")
  | .error error =>
      assertTrue (decide (error.site = .occurrence expression.occurrence) &&
          match error.reason with
          | .requirementsPresent [actual] => actual == requirement
          | _ => false)
        s!"required unary compatibility rejection changed: {reprStr error}"
  let draft ← match
      SourceCoreElaboration.lowerFunctionBodyWithRuntimePolicies id
        SourceCoreElaboration.rejectCalls
        (requiredWordUnaryPolicy [requirement])
        SourceCoreElaboration.rejectRequiredBinaries
        SourceCoreElaboration.rejectCoercions required with
    | .ok draft => pure draft
    | .error error => throw (IO.userError
        s!"required unary policy did not lower: {reprStr error}")
  let lowered ← match draft.finalize with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"required unary policy did not finalize: {reprStr error}")
  assertTrue (decide (Core.runStateful 100
      (.initial lowered.core [.word (word 4)]) =
        .done (.word (word 4).bitNot) []))
    "required unary policy changed operand traversal or runtime meaning"
  match SourceCoreElaboration.lowerFunctionBodyWithRuntimePolicies id
      SourceCoreElaboration.rejectCalls (requiredWordUnaryPolicy [])
      SourceCoreElaboration.rejectRequiredBinaries
      SourceCoreElaboration.rejectCoercions required with
  | .ok _ => throw (IO.userError
      "required unary policy accepted mismatched requirement identities")
  | .error error =>
      assertTrue (decide (error.site = .occurrence expression.occurrence) &&
          match error.reason with
          | .unaryRequirementsMismatch [expected] [] =>
              expected == requirement
          | _ => false)
        s!"required unary mismatch reported the wrong error: {reprStr error}"

private def testCallAwareCompatibility : IO Unit := do
  let program ← checkedProgram (String.intercalate "\n" [
    "function callee(value: Word) returns (Word) { return value; }",
    "function caller(value: Word) returns (Word) { return callee(value); }"
  ])
  let function ← checkedNamed program "caller"
  let onCall : SourceCoreElaboration.CallElaborator
      SourceCoreElaboration.Error :=
    fun _ node _ _ _ => pure {
      argumentTypes := [.word]
      consumedRequirements := []
      build := fun arguments =>
        match arguments with
        | [argument] => pure argument
        | arguments => throw {
            site := .occurrence node.id.occurrence
            reason := .callArgumentArityMismatch 1 arguments.length
          }
    }
  let draft ← match SourceCoreElaboration.lowerFunctionBodyWith id onCall
      function with
    | .ok draft => pure draft
    | .error error => throw (IO.userError
        s!"call-aware compatibility wrapper did not lower: {reprStr error}")
  let lowered ← match draft.finalize with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"call-aware compatibility wrapper did not finalize: {reprStr error}")
  assertTrue (decide (Core.runStateful 100
      (.initial lowered.core [.word (word 19)]) =
        .done (.word (word 19)) []))
    "call-aware compatibility wrapper changed its custom call semantics"

private def testCoercionPolicy : IO Unit := do
  let program ← checkedProgram
    "function coerced(x: Word) returns (Word) { return x + 1; }"
  let function ← checkedNamed program "coerced"
  let (_, expression) ← rootIds function
  let root ← match function.typedBody.lookupExpression? expression with
    | some node => pure node
    | none => throw (IO.userError "coercion fixture lost its root expression")
  let left ← match root.form with
    | .binary left .add _ => pure left
    | _ => throw (IO.userError "coercion fixture root is not addition")
  let binaryRequirement : RequirementId := ⟨201⟩
  let firstCoercion : RequirementId := ⟨202⟩
  let secondCoercion : RequirementId := ⟨203⟩
  let solved := [
    solvedWordRequirement function.declaration binaryRequirement,
    solvedWordRequirement function.declaration firstCoercion,
    solvedWordRequirement function.declaration secondCoercion
  ]
  let rootCoerced : CheckedFunction := {
    function with
    solvedRequirements := solved
    typedBody := changeExpression function.typedBody expression fun node => {
      node with
      requirements := [secondCoercion, binaryRequirement, firstCoercion]
      coercions := [
        { requirement := firstCoercion, source := .word, target := .bool },
        { requirement := secondCoercion, source := .bool, target := .word }
      ]
    }
  }
  let rootDraft ← match
      SourceCoreElaboration.lowerFunctionBodyWithAllPolicies id
        SourceCoreElaboration.rejectCalls
        (requiredWordBinaryPolicy [binaryRequirement])
        executableCoercionPolicy rootCoerced with
    | .ok draft => pure draft
    | .error error => throw (IO.userError
        s!"root coercion policy did not lower: {reprStr error}")
  let rootLowered ← match rootDraft.finalize with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"root coercion policy did not finalize: {reprStr error}")
  assertTrue (decide (Core.runStateful 100
      (.initial rootLowered.core [.word (word 4)]) =
        .done (.word (word 1)) []))
    "coercion requirements were removed positionally or plans ran out of order"

  let childCoerced : CheckedFunction := {
    function with
    solvedRequirements := solved
    typedBody :=
      changeExpression
        (changeExpression function.typedBody expression fun node => {
          node with requirements := [binaryRequirement]
        }) left fun node => {
          node with
          requirements := [firstCoercion, secondCoercion]
          coercions := [
            { requirement := firstCoercion, source := .word, target := .bool },
            { requirement := secondCoercion, source := .bool, target := .word }
          ]
        }
  }
  let childDraft ← match
      SourceCoreElaboration.lowerFunctionBodyWithAllPolicies id
        SourceCoreElaboration.rejectCalls
        (requiredWordBinaryPolicy [binaryRequirement])
        executableCoercionPolicy childCoerced with
    | .ok draft => pure draft
    | .error error => throw (IO.userError
        s!"required-binary child coercion did not lower: {reprStr error}")
  let childLowered ← match childDraft.finalize with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"required-binary child coercion did not finalize: {reprStr error}")
  assertTrue (decide (Core.runStateful 100
      (.initial childLowered.core [.word (word 4)]) =
        .done (.word (word 2)) []))
    "required-binary traversal did not recursively execute child coercions"

private def testMalformedCoercionPolicies : IO Unit := do
  let program ← checkedProgram
    "function identity(x: Word) returns (Word) { return x; }"
  let function ← checkedNamed program "identity"
  let (_, expression) ← rootIds function
  let first : RequirementId := ⟨301⟩
  let second : RequirementId := ⟨302⟩
  let changed (requirements : List RequirementId)
      (coercions : List CoercionStep) : CheckedFunction :=
    withExpression function expression fun node => {
      node with requirements, coercions
    }
  expectCoercionPolicyError "identity coercion step"
    (changed [first] [{ requirement := first, source := .word, target := .word }])
    expression executableCoercionPolicy fun reason => match reason with
      | .identityCoercionStep 0 actual .word => actual == first
      | _ => false
  expectCoercionPolicyError "discontinuous coercion path"
    (changed [first, second] [
      { requirement := first, source := .word, target := .bool },
      { requirement := second, source := .word, target := .bool }
    ]) expression executableCoercionPolicy fun reason => match reason with
      | .coercionPathDiscontinuity 1 .bool .word => true
      | _ => false
  expectCoercionPolicyError "wrong coercion target"
    (changed [first]
      [{ requirement := first, source := .word, target := .bool }])
    expression executableCoercionPolicy fun reason => match reason with
      | .coercionPathTargetMismatch .word .bool => true
      | _ => false
  expectCoercionPolicyError "missing coercion requirement"
    (changed [first] [
      { requirement := first, source := .word, target := .bool },
      { requirement := second, source := .bool, target := .word }
    ]) expression executableCoercionPolicy fun reason => match reason with
      | .missingCoercionRequirement actual [attached] =>
          actual == second && attached == first
      | _ => false
  expectCoercionPolicyError "duplicate coercion requirement"
    (changed [first] [
      { requirement := first, source := .word, target := .bool },
      { requirement := first, source := .bool, target := .word }
    ]) expression executableCoercionPolicy fun reason => match reason with
      | .duplicateCoercionRequirement actual => actual == first
      | _ => false
  let valid := changed [first, second] [
    { requirement := first, source := .word, target := .bool },
    { requirement := second, source := .bool, target := .word }
  ]
  expectCoercionPolicyError "coercion plan source"
    valid expression (constantCoercionPolicy .bool .bool [first])
    fun reason => match reason with
      | .coercionPlanSourceTypeMismatch actual .word .bool => actual == first
      | _ => false
  expectCoercionPolicyError "coercion plan target"
    valid expression (constantCoercionPolicy .word .word [first])
    fun reason => match reason with
      | .coercionPlanTargetTypeMismatch actual .bool .word => actual == first
      | _ => false
  expectCoercionPolicyError "coercion plan requirements"
    valid expression (constantCoercionPolicy .word .bool [])
    fun reason => match reason with
      | .coercionPlanRequirementsMismatch actual [expected] [] =>
          actual == first && expected == first
      | _ => false

private def testUnsupportedExpressions (function : CheckedFunction) : IO Unit := do
  let (_, expression) ← rootIds function
  let cases : List
      (String × ExpressionForm × SourceCoreElaboration.UnsupportedExpression) := [
    ("call", .call expression [] (.indirect {
      argumentTypeBeforeCoercion := .unit
      argumentTypeAfterCoercion := .unit
    }), .call),
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
  testRequiredBinaryPolicy
  testRequiredUnaryPolicy
  testCallAwareCompatibility
  testCoercionPolicy
  testMalformedCoercionPolicies
  testUnsupportedExpressions function
  testBrokenEdges function
  testUnsupportedTypesAndDuplicateInputs function
  testTypeMismatchAndUnconsumedRequirement function
  testOverflowLiteral

end Tests.SourceCoreElaboration
