import Solcore
import Solcore.Test.Frontend.Source.CompilerFeatureSupport

/-!
# Staged source tests

Closed staged values, conditionals, value calls, marked methods, required operators and recursion, with
their tamper checks.
-/

section
-- leanmerge: from Solcore.Test.SourceStagedConditionals
/-! End-to-end regressions for closed staged conditionals. -/

set_option autoImplicit false

namespace Tests.SourceStagedConditionals

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceProgramExecution Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | none => throw (IO.userError "invalid staged-conditional module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"staged-conditional fixture failed checking: {reprStr errors}")

private def checkedNamed (program : CheckedProgram) (name : String) :
    IO CheckedFunction :=
  match program.functions.find? fun function =>
      (program.environment.declaration? function.declaration).any fun entry =>
        entry.name == some name with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def signatureNamed (program : CheckedProgram) (name : String) :
    IO ProgramFunctionSignature :=
  match program.signatures.functions.find? fun signature =>
      signature.name == name with
  | some signature => pure signature
  | none => throw (IO.userError s!"signature `{name}` was not found")

private def returnedExpression (function : CheckedFunction) : IO ExpressionId :=
  match function.typedBody.roots with
  | [.statement statement] =>
      match function.typedBody.lookupStatement? statement with
      | some { form := .returnStmt (some expression), .. } => pure expression
      | _ => throw (IO.userError
          "staged-conditional root is not a valued return")
  | roots => throw (IO.userError
      s!"staged-conditional fixture retained {roots.length} roots")

private def callArguments (function : CheckedFunction) (id : ExpressionId)
    (expected : BuiltinFunctionId) : IO (List ExpressionId) :=
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .call callee arguments (.builtinFunction actual) => do
          let calleeValid := match function.typedBody.lookupExpression? callee with
            | some calleeNode =>
                match calleeNode.form with
                | .reference spelling (.builtinFunction calleeIdentity) =>
                    calleeIdentity == expected &&
                      spelling == expected.spelling &&
                      calleeNode.type == expected.type &&
                      calleeNode.requirements.isEmpty &&
                      calleeNode.coercions.isEmpty
                | _ => false
            | none => false
          assertTrue (actual == expected && node.type == expected.returnType &&
              node.requirements.isEmpty && node.coercions.isEmpty && calleeValid)
            s!"builtin call `{expected.spelling}` lost exact metadata"
          pure arguments
      | _ => throw (IO.userError
          s!"expected builtin call `{expected.spelling}`, found {reprStr node}")
  | none => throw (IO.userError
      s!"builtin call `{expected.spelling}` was absent")

private def conditionalChildren (function : CheckedFunction)
    (id : ExpressionId) (expected : Ty) :
    IO (ExpressionId × ExpressionId × ExpressionId) :=
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .conditional condition thenBranch elseBranch => do
          assertTrue (node.type == expected && node.requirements.isEmpty &&
              node.coercions.isEmpty)
            "conditional lost its exact type or empty occurrence metadata"
          pure (condition, thenBranch, elseBranch)
      | _ => throw (IO.userError
          s!"expected conditional expression, found {reprStr node}")
  | none => throw (IO.userError "conditional expression was absent")

private def literalRequirement (function : CheckedFunction)
    (id : ExpressionId) (expectedType : Ty) : IO RequirementId :=
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .integerLiteral _ resolution => do
          assertTrue (node.type == expectedType &&
              resolution.targetType == expectedType &&
              node.requirements == [resolution.requirement] &&
              node.coercions.isEmpty)
            "conditional literal lost its target or requirement attachment"
          pure resolution.requirement
      | _ => throw (IO.userError
          s!"conditional child is not an integer literal: {reprStr node}")
  | none => throw (IO.userError "conditional literal was absent")

private def positiveSource : String := String.intercalate "\n" [
  "function ordered() returns (Word) {",
  "  return wordFromInteger(integerLt(1, 2) ? integerSub(10, 3) : integerAdd(20, 4));",
  "}",
  "function integerElse() returns (Word) {",
  "  return wordFromInteger(false ? integerSub(30, 5) : integerAdd(20, 2));",
  "}",
  "function negativeComparison() returns (Word) {",
  "  return wordFromInteger(integerLt(integerSub(0, 2), integerSub(0, 1)) ? 33 : 44);",
  "}",
  "function wordConditional() returns (Word) {",
  "  return wordFromInteger(wordToInteger(false ? 7 : 9));",
  "}",
  "function boolConditional() returns (Word) {",
  "  return wordFromInteger((true ? false : true) ? 11 : 12);",
  "}",
  "function nestedGrouped() returns (Word) {",
  "  return wordFromInteger(((integerEq((1), (1)) ? (integerMul((2), (3))) : (integerSub((9), (4))))));",
  "}"
]

private def limits : Limits := {
  checkingFuel := 1024
  specializationBudget := 1
  executionFuel := 1024
}

private def testIntegerConditionalCarrier : IO Unit := do
  let program ← checkedProgram positiveSource
  let function ← checkedNamed program "ordered"
  let root ← returnedExpression function
  let outer ← callArguments function root .wordFromInteger
  let conditional ← match outer with
    | [conditional] => pure conditional
    | arguments => throw (IO.userError
        s!"wordFromInteger retained {arguments.length} arguments")
  let (guard, thenBranch, elseBranch) ←
    conditionalChildren function conditional Ty.integer
  let guardArguments ← callArguments function guard .integerLt
  let thenArguments ← callArguments function thenBranch .integerSub
  let elseArguments ← callArguments function elseBranch .integerAdd
  let (guardLeft, guardRight, thenLeft, thenRight, elseLeft, elseRight) ←
    match guardArguments, thenArguments, elseArguments with
    | [guardLeft, guardRight], [thenLeft, thenRight], [elseLeft, elseRight] =>
        pure (guardLeft, guardRight, thenLeft, thenRight, elseLeft, elseRight)
    | _, _, _ => throw (IO.userError
        "conditional arithmetic lost its exact binary arguments")
  let mut expectedRequirements : List RequirementId := []
  for literal in [guardLeft, guardRight, thenLeft, thenRight, elseLeft,
      elseRight] do
    expectedRequirements := expectedRequirements ++
      [← literalRequirement function literal Ty.integer]
  assertTrue (function.solvedRequirements.map (·.id) == expectedRequirements)
    "conditional literal requirements changed source order"
  match SourceCoreElaboration.evaluateStagedBool function.solvedRequirements
      function.typedBody guard with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = true ∧
          evaluated.consumedRequirements = expectedRequirements.take 2))
        "comparison guard did not evaluate as a closed Bool"
  | .error error => throw (IO.userError
      s!"comparison guard did not stage: {reprStr error}")
  match SourceCoreElaboration.evaluateStagedInteger function.solvedRequirements
      function.typedBody conditional with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (7 : Int) ∧
          evaluated.consumedRequirements = expectedRequirements))
        "integer conditional lost selected value or all-branch requirement order"
  | .error error => throw (IO.userError
      s!"integer conditional did not stage: {reprStr error}")
  let signature ← signatureNamed program "ordered"
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] 1 with
  | .ok (.complete plan) =>
      assertTrue (plan.specializations.length == 1 && plan.callEdges.isEmpty)
        "staged conditional created source call edges"
  | result => throw (IO.userError
      s!"staged-conditional worklist did not close in one slot: {reprStr result}")

private def testWordAndBoolConditionalCarriers : IO Unit := do
  let program ← checkedProgram positiveSource
  let wordFunction ← checkedNamed program "wordConditional"
  let wordRoot ← returnedExpression wordFunction
  let wordOuter ← callArguments wordFunction wordRoot .wordFromInteger
  let conversion ← match wordOuter with
    | [conversion] => pure conversion
    | arguments => throw (IO.userError
        s!"word conditional retained {arguments.length} outer arguments")
  let conversionArguments ← callArguments wordFunction conversion .wordToInteger
  let wordConditional ← match conversionArguments with
    | [conditional] => pure conditional
    | arguments => throw (IO.userError
        s!"wordToInteger retained {arguments.length} arguments")
  let (_, wordThen, wordElse) ←
    conditionalChildren wordFunction wordConditional Ty.word
  let thenRequirement ← literalRequirement wordFunction wordThen Ty.word
  let elseRequirement ← literalRequirement wordFunction wordElse Ty.word
  let wordRequirements := [thenRequirement, elseRequirement]
  assertTrue (decide (wordFunction.solvedRequirements.map (·.id) =
      wordRequirements))
    "Word conditional changed branch requirement order"
  match SourceCoreElaboration.evaluateStagedWord
      wordFunction.solvedRequirements wordFunction.typedBody wordConditional with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = Core.Word.ofNatModulo 9 ∧
          evaluated.consumedRequirements = wordRequirements))
        "Word conditional lost its selected value or unselected requirement"
  | .error error => throw (IO.userError
      s!"Word conditional did not stage: {reprStr error}")

  let boolFunction ← checkedNamed program "boolConditional"
  let boolRoot ← returnedExpression boolFunction
  let boolOuter ← callArguments boolFunction boolRoot .wordFromInteger
  let integerConditional ← match boolOuter with
    | [conditional] => pure conditional
    | arguments => throw (IO.userError
        s!"Bool fixture retained {arguments.length} outer arguments")
  let (boolConditional, _, _) ←
    conditionalChildren boolFunction integerConditional Ty.integer
  let boolConditionalBody ←
    match boolFunction.typedBody.lookupExpression? boolConditional with
    | some { form := .group inner, .. } => pure inner
    | _ => pure boolConditional
  let (_, boolThen, boolElse) ←
    conditionalChildren boolFunction boolConditionalBody Ty.bool
  for (id, expectedName, expectedValue) in
      [(boolThen, "false", false), (boolElse, "true", true)] do
    match boolFunction.typedBody.lookupExpression? id with
    | some node =>
        match node.form with
        | .reference name (.builtinBoolean value) =>
            assertTrue (name == expectedName && value == expectedValue &&
                node.type == Ty.bool && node.requirements.isEmpty &&
                node.coercions.isEmpty)
              "builtin Bool branch lost spelling, identity, or metadata"
        | _ => throw (IO.userError
            s!"builtin Bool branch changed form: {reprStr node}")
    | none => throw (IO.userError "builtin Bool branch was absent")
  match SourceCoreElaboration.evaluateStagedBool boolFunction.solvedRequirements
      boolFunction.typedBody boolConditional with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = false ∧
          evaluated.consumedRequirements = []))
        "Bool conditional did not select false after validating both branches"
  | .error error => throw (IO.userError
      s!"Bool conditional did not stage: {reprStr error}")

private def assertPublicWord (moduleId : Workspace.ModuleId)
    (name : String) (expected : Core.Word) : IO Unit := do
  let prepared ← match prepare (workspace positiveSource)
      (Seed.named moduleId name) limits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"{name}: public preparation failed: {reprStr error}")
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .word expected ∧
      prepared.entry.elaborated.core = .word expected))
    s!"{name}: closed conditional was not erased to one Word constant"
  let store : Core.Store := [.bool true, .word (Core.Word.ofNatModulo 91)]
  assertTrue (decide (prepared.run? [] limits.executionFuel store =
      some (.done (.word expected) store)))
    s!"{name}: staged conditional changed its value or store"

private def testPublicExecution : IO Unit := do
  let moduleId ← mainModule
  let cases : List (String × Core.Word) := [
    ("ordered", Core.Word.ofNatModulo 7),
    ("integerElse", Core.Word.ofNatModulo 22),
    ("negativeComparison", Core.Word.ofNatModulo 33),
    ("wordConditional", Core.Word.ofNatModulo 9),
    ("boolConditional", Core.Word.ofNatModulo 12),
    ("nestedGrouped", Core.Word.ofNatModulo 6)
  ]
  for (name, expected) in cases do
    assertPublicWord moduleId name expected
  let program ← checkedProgram positiveSource
  let grouped ← checkedNamed program "nestedGrouped"
  assertTrue (decide (grouped.typedBody.nodes.countP (fun
      | .expression { form := .group _, .. } => true
      | _ => false) >= 6))
    "nested/grouped conditional fixture lost transparent group nodes"

private def expectPublicSourceCoreError (label content name : String)
    (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId name) limits with
  | .error (.linking (.sourceCore error)) =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong public source-Core error {reprStr error}"
  | result => throw (IO.userError
      s!"{label}: closedness violation was not rejected: {reprStr result}")

private def testClosednessRejections : IO Unit := do
  let runtimeGuardSource :=
    "function dependent(flag: Bool) returns (Word) { return wordFromInteger(flag ? 1 : 2); }"
  let guardProgram ← checkedProgram runtimeGuardSource
  let guardFunction ← checkedNamed guardProgram "dependent"
  let guardRoot ← returnedExpression guardFunction
  let guardOuter ← callArguments guardFunction guardRoot .wordFromInteger
  let guardConditional ← match guardOuter with
    | [conditional] => pure conditional
    | _ => throw (IO.userError "runtime guard fixture lost its conditional")
  let (runtimeGuard, _, _) ←
    conditionalChildren guardFunction guardConditional Ty.integer
  expectPublicSourceCoreError "runtime-dependent guard" runtimeGuardSource
    "dependent" (.occurrence runtimeGuard.occurrence) fun reason =>
      reason == .stagedBoolExpressionNotClosed

  let deadBranchSource :=
    "function dead(value: Word) returns (Word) { return wordFromInteger(true ? 1 : wordToInteger(value)); }"
  let deadProgram ← checkedProgram deadBranchSource
  let deadFunction ← checkedNamed deadProgram "dead"
  let deadRoot ← returnedExpression deadFunction
  let deadOuter ← callArguments deadFunction deadRoot .wordFromInteger
  let deadConditional ← match deadOuter with
    | [conditional] => pure conditional
    | _ => throw (IO.userError "dead-branch fixture lost its conditional")
  let (_, _, deadElse) ←
    conditionalChildren deadFunction deadConditional Ty.integer
  let deadArguments ← callArguments deadFunction deadElse .wordToInteger
  let runtimeWord ← match deadArguments with
    | [runtimeWord] => pure runtimeWord
    | _ => throw (IO.userError "dead branch lost its runtime Word reference")
  expectPublicSourceCoreError "unselected runtime-dependent branch"
    deadBranchSource "dead" (.occurrence runtimeWord.occurrence) fun reason =>
      reason == .stagedWordExpressionNotClosed

/-- Exercise Int, Word, and Bool conditional staging through the public runner. -/
def testSourceStagedConditionals : IO Unit := do
  testIntegerConditionalCarrier
  testWordAndBoolConditionalCarriers
  testPublicExecution
  testClosednessRejections
  IO.println "closed staged conditional checks GREEN"

end Tests.SourceStagedConditionals
end

section
-- leanmerge: from Solcore.Test.SourceStagedConditionalsTamper
/-! Adversarial regressions for closed staged-conditional metadata. -/

set_option autoImplicit false

namespace Tests.SourceStagedConditionalsTamper

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def checkedFunction (content : String) : IO CheckedFunction := do
  let program ← match checkProgram (workspace content) with
    | .ok program => pure program
    | .error errors => throw (IO.userError
        s!"staged-conditional tamper fixture failed checking: {reprStr errors}")
  match program.functions with
  | [function] => pure function
  | functions => throw (IO.userError
      s!"staged-conditional fixture produced {functions.length} functions")

private def returnedExpression (function : CheckedFunction) : IO ExpressionId :=
  match function.typedBody.roots with
  | [.statement statement] =>
      match function.typedBody.lookupStatement? statement with
      | some { form := .returnStmt (some expression), .. } => pure expression
      | _ => throw (IO.userError "tamper fixture lost its valued return")
  | _ => throw (IO.userError "tamper fixture lost its unique root")

private def unaryBuiltinArgument (function : CheckedFunction)
    (id : ExpressionId) (expected : BuiltinFunctionId) : IO ExpressionId :=
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .call _ [argument] (.builtinFunction actual) =>
          if actual == expected then pure argument
          else throw (IO.userError
            s!"expected `{expected.spelling}`, found `{actual.spelling}`")
      | _ => throw (IO.userError
          s!"expected unary builtin `{expected.spelling}`: {reprStr node}")
  | none => throw (IO.userError "unary builtin node was absent")

private def binaryBuiltin (function : CheckedFunction) (id : ExpressionId)
    (expected : BuiltinFunctionId) :
    IO (ExpressionId × ExpressionId × ExpressionId) :=
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .call callee [left, right] (.builtinFunction actual) =>
          if actual == expected then pure (callee, left, right)
          else throw (IO.userError
            s!"expected `{expected.spelling}`, found `{actual.spelling}`")
      | _ => throw (IO.userError
          s!"expected binary builtin `{expected.spelling}`: {reprStr node}")
  | none => throw (IO.userError "binary builtin node was absent")

private def conditional (function : CheckedFunction) (id : ExpressionId) :
    IO (ExpressionId × ExpressionId × ExpressionId) :=
  match function.typedBody.lookupExpression? id with
  | some { form := .conditional condition thenBranch elseBranch, .. } =>
      pure (condition, thenBranch, elseBranch)
  | node => throw (IO.userError
      s!"conditional node changed shape: {reprStr node}")

private def literalResolution (function : CheckedFunction)
    (id : ExpressionId) : IO IntegerLiteralResolution :=
  match function.typedBody.lookupExpression? id with
  | some { form := .integerLiteral _ resolution, .. } => pure resolution
  | node => throw (IO.userError
      s!"literal node changed shape: {reprStr node}")

private def changeExpression (source : TypedSource) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : TypedSource := {
  source with
  nodes := source.nodes.map fun
    | .expression node =>
        if node.id = id then .expression { change node with id }
        else .expression node
    | .statement node => .statement node
}

private def withExpression (function : CheckedFunction) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : CheckedFunction := {
  function with typedBody := changeExpression function.typedBody id change
}

private def expectElaborationErrorAt (label : String)
    (function : CheckedFunction) (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.elaborateFunction function with
  | .ok _ => throw (IO.userError
      s!"{label}: malformed conditional reached Semantic Core")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong elaboration error {reprStr error}"

private def expectIntegerErrorAt (label : String)
    (function : CheckedFunction) (id : ExpressionId)
    (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedInteger
      function.solvedRequirements function.typedBody id with
  | .ok value => throw (IO.userError
      s!"{label}: malformed conditional evaluated to {reprStr value}")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong staged-Integer error {reprStr error}"

private def expectWordErrorAt (label : String) (function : CheckedFunction)
    (id : ExpressionId) (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedWord
      function.solvedRequirements function.typedBody id with
  | .ok value => throw (IO.userError
      s!"{label}: malformed Word conditional evaluated to {reprStr value}")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong staged-Word error {reprStr error}"

private def expectBoolErrorAt (label : String) (function : CheckedFunction)
    (id : ExpressionId) (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedBool
      function.solvedRequirements function.typedBody id with
  | .ok value => throw (IO.userError
      s!"{label}: malformed Bool conditional evaluated to {reprStr value}")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong staged-Bool error {reprStr error}"

private structure IntegerFixture where
  function : CheckedFunction
  root : ExpressionId
  conditional : ExpressionId
  guard : ExpressionId
  guardCallee : ExpressionId
  guardLeft : ExpressionId
  guardRight : ExpressionId
  thenBranch : ExpressionId
  thenLeft : ExpressionId
  thenRight : ExpressionId
  elseBranch : ExpressionId
  elseCallee : ExpressionId
  elseLeft : ExpressionId
  elseRight : ExpressionId
  elseLeftResolution : IntegerLiteralResolution

private def integerFixture : IO IntegerFixture := do
  let function ← checkedFunction
    "function tamper() returns (Word) { return wordFromInteger(integerLt(1, 2) ? integerSub(10, 3) : integerAdd(20, 4)); }"
  let root ← returnedExpression function
  let conditionalId ← unaryBuiltinArgument function root .wordFromInteger
  let (guard, thenBranch, elseBranch) ← conditional function conditionalId
  let (guardCallee, guardLeft, guardRight) ←
    binaryBuiltin function guard .integerLt
  let (_, thenLeft, thenRight) ←
    binaryBuiltin function thenBranch .integerSub
  let (elseCallee, elseLeft, elseRight) ←
    binaryBuiltin function elseBranch .integerAdd
  let elseLeftResolution ← literalResolution function elseLeft
  pure {
    function
    root
    conditional := conditionalId
    guard
    guardCallee
    guardLeft
    guardRight
    thenBranch
    thenLeft
    thenRight
    elseBranch
    elseCallee
    elseLeft
    elseRight
    elseLeftResolution
  }

private def intCoercion (fixture : IntegerFixture) : CoercionStep := {
  requirement := fixture.elseLeftResolution.requirement
  source := Ty.integer
  target := Ty.word
}

private def testIntegerBaselineAndParentMetadata
    (fixture : IntegerFixture) : IO Unit := do
  let expected := fixture.function.solvedRequirements.map (·.id)
  match SourceCoreElaboration.evaluateStagedInteger
      fixture.function.solvedRequirements fixture.function.typedBody
      fixture.conditional with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (7 : Int) ∧
          evaluated.consumedRequirements = expected ∧
          expected.length = 6))
        "integer conditional baseline lost all-branch requirement order"
  | .error error => throw (IO.userError
      s!"integer conditional baseline failed: {reprStr error}")
  let site := SourceCoreElaboration.ErrorSite.occurrence
    fixture.conditional.occurrence
  let requirement := fixture.elseLeftResolution.requirement
  let wrongType := withExpression fixture.function fixture.conditional fun node =>
    { node with type := Ty.word }
  expectIntegerErrorAt "conditional result type" wrongType fixture.conditional
    site fun reason => reason == .stagedIntegerTypeMismatch Ty.integer Ty.word
  let requirements := withExpression fixture.function fixture.conditional
    fun node => { node with requirements := [requirement] }
  expectIntegerErrorAt "conditional own requirements" requirements
    fixture.conditional site fun reason =>
      reason == .requirementsPresent [requirement]
  let coercions := withExpression fixture.function fixture.conditional
    fun node => { node with coercions := [intCoercion fixture] }
  expectIntegerErrorAt "conditional own coercions" coercions
    fixture.conditional site fun reason =>
      reason == .coercionsPresent [intCoercion fixture]

private def testIntegerChildrenAndUnselectedValidation
    (fixture : IntegerFixture) : IO Unit := do
  let guardSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.guard.occurrence
  let thenLiteralSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.thenLeft.occurrence
  let wrongGuardEdge := withExpression fixture.function fixture.conditional
    fun node => { node with form := match node.form with
      | .conditional _ thenBranch elseBranch =>
          .conditional fixture.thenLeft thenBranch elseBranch
      | form => form }
  expectIntegerErrorAt "conditional guard type" wrongGuardEdge
    fixture.conditional thenLiteralSite fun reason =>
      reason == .stagedBoolTypeMismatch Ty.bool Ty.integer
  let wrongBranchEdge := withExpression fixture.function fixture.conditional
    fun node => { node with form := match node.form with
      | .conditional condition _ elseBranch =>
          .conditional condition fixture.guard elseBranch
      | form => form }
  expectIntegerErrorAt "conditional branch type" wrongBranchEdge
    fixture.conditional guardSite fun reason =>
      reason == .stagedIntegerTypeMismatch Ty.integer Ty.bool

  let requirement := fixture.elseLeftResolution.requirement
  let expectedPredicate := fixture.elseLeftResolution.predicate
  let forgedEvidence : CheckedFunction := {
    fixture.function with
    solvedRequirements := fixture.function.solvedRequirements.map fun solved =>
      if solved.id = requirement then {
        solved with evidence := (.implementation
          (.byImpl expectedPredicate (.builtin .intWord) []))
      } else solved
  }
  expectIntegerErrorAt "unselected branch evidence" forgedEvidence
    fixture.conditional (.occurrence fixture.elseLeft.occurrence) fun reason =>
      reason == .integerLiteralImplementationMismatch requirement
        (.builtin .intInteger) (.builtin .intWord)

  let forgedSpelling := withExpression fixture.function fixture.elseCallee
    fun node => { node with form := match node.form with
      | .reference _ resolution => .reference "forgedIntegerAdd" resolution
      | form => form }
  expectIntegerErrorAt "unselected branch builtin spelling" forgedSpelling
    fixture.conditional (.occurrence fixture.elseCallee.occurrence) fun reason =>
      reason == .builtinFunctionCalleeSpellingMismatch .integerAdd
        BuiltinFunctionId.integerAdd.spelling "forgedIntegerAdd"

  let sharedBranch := withExpression fixture.function fixture.conditional
    fun node => { node with form := match node.form with
      | .conditional condition thenBranch _ =>
          .conditional condition thenBranch thenBranch
      | form => form }
  let thenResolution ← literalResolution fixture.function fixture.thenLeft
  expectElaborationErrorAt "shared conditional branch" sharedBranch
    (.declaration fixture.function.declaration) fun reason =>
      reason == .duplicateConsumedRequirement thenResolution.requirement

private def testIntegerAndConditionCycles (fixture : IntegerFixture) : IO Unit := do
  let conditionCycle := withExpression fixture.function fixture.guard fun node =>
    { node with form := .group fixture.guard, requirements := [] }
  expectIntegerErrorAt "conditional guard cycle" conditionCycle
    fixture.conditional (.occurrence fixture.guard.occurrence) fun reason =>
      reason == .stagedBoolDepthLimit
  let branchCycle := withExpression fixture.function fixture.conditional
    fun node => { node with form := match node.form with
      | .conditional condition _ elseBranch =>
          .conditional condition fixture.conditional elseBranch
      | form => form }
  match SourceCoreElaboration.evaluateStagedInteger
      branchCycle.solvedRequirements branchCycle.typedBody
      fixture.conditional with
  | .error error =>
      match error.site, error.reason with
      | .occurrence occurrence, .stagedIntegerDepthLimit =>
          assertTrue (occurrence.owner == fixture.conditional.occurrence.owner)
            "conditional branch cycle escaped its declaration"
      | _, _ => throw (IO.userError
          s!"conditional branch cycle produced the wrong error: {reprStr error}")
  | result => throw (IO.userError
      s!"conditional branch cycle produced the wrong result: {reprStr result}")

private structure BoolFixture where
  function : CheckedFunction
  conditional : ExpressionId
  condition : ExpressionId
  thenBranch : ExpressionId
  elseBranch : ExpressionId
  requirement : RequirementId

private def boolFixture : IO BoolFixture := do
  let function ← checkedFunction
    "function bools() returns (Word) { return wordFromInteger((true ? false : true) ? 1 : 2); }"
  let root ← returnedExpression function
  let integerConditional ← unaryBuiltinArgument function root .wordFromInteger
  let (boolConditionalGroup, integerThen, _) ←
    conditional function integerConditional
  let boolConditional ←
    match function.typedBody.lookupExpression? boolConditionalGroup with
    | some { form := .group inner, .. } => pure inner
    | _ => pure boolConditionalGroup
  let (condition, thenBranch, elseBranch) ←
    conditional function boolConditional
  let resolution ← literalResolution function integerThen
  pure {
    function
    conditional := boolConditional
    condition
    thenBranch
    elseBranch
    requirement := resolution.requirement
  }

private def testBoolMetadataSpellingAndCycle (fixture : BoolFixture) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedBool
      fixture.function.solvedRequirements fixture.function.typedBody
      fixture.conditional with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = false ∧
          evaluated.consumedRequirements = []))
        "Bool conditional baseline changed"
  | .error error => throw (IO.userError
      s!"Bool conditional baseline failed: {reprStr error}")
  let site := SourceCoreElaboration.ErrorSite.occurrence
    fixture.conditional.occurrence
  let coercion : CoercionStep := {
    requirement := fixture.requirement
    source := Ty.bool
    target := Ty.integer
  }
  let wrongType := withExpression fixture.function fixture.conditional fun node =>
    { node with type := Ty.integer }
  expectBoolErrorAt "Bool conditional type" wrongType fixture.conditional site
    fun reason => reason == .stagedBoolTypeMismatch Ty.bool Ty.integer
  let requirements := withExpression fixture.function fixture.conditional
    fun node => { node with requirements := [fixture.requirement] }
  expectBoolErrorAt "Bool conditional requirements" requirements
    fixture.conditional site fun reason =>
      reason == .requirementsPresent [fixture.requirement]
  let coercions := withExpression fixture.function fixture.conditional
    fun node => { node with coercions := [coercion] }
  expectBoolErrorAt "Bool conditional coercions" coercions fixture.conditional
    site fun reason => reason == .coercionsPresent [coercion]
  let referenceSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.elseBranch.occurrence
  let referenceType := withExpression fixture.function fixture.elseBranch
    fun node => { node with type := Ty.integer }
  expectBoolErrorAt "builtin Bool reference type" referenceType
    fixture.conditional referenceSite fun reason =>
      reason == .stagedBoolTypeMismatch Ty.bool Ty.integer
  let referenceRequirements :=
    withExpression fixture.function fixture.elseBranch fun node =>
      { node with requirements := [fixture.requirement] }
  expectBoolErrorAt "builtin Bool reference requirements"
    referenceRequirements fixture.conditional referenceSite fun reason =>
      reason == .requirementsPresent [fixture.requirement]
  let referenceCoercions :=
    withExpression fixture.function fixture.elseBranch fun node =>
      { node with coercions := [coercion] }
  expectBoolErrorAt "builtin Bool reference coercions" referenceCoercions
    fixture.conditional referenceSite fun reason =>
      reason == .coercionsPresent [coercion]
  let spelling := withExpression fixture.function fixture.thenBranch fun node =>
    { node with form := match node.form with
      | .reference _ resolution => .reference "forgedFalse" resolution
      | form => form }
  expectBoolErrorAt "builtin Bool spelling" spelling fixture.conditional
    (.occurrence fixture.thenBranch.occurrence) fun reason =>
      reason == .builtinBooleanSpellingMismatch false "false" "forgedFalse"
  let cycle := withExpression fixture.function fixture.conditional fun node =>
    { node with form := match node.form with
      | .conditional condition _ elseBranch =>
          .conditional condition fixture.conditional elseBranch
      | form => form }
  match SourceCoreElaboration.evaluateStagedBool cycle.solvedRequirements
      cycle.typedBody fixture.conditional with
  | .error error =>
      match error.site, error.reason with
      | .occurrence occurrence, .stagedBoolDepthLimit =>
          assertTrue (occurrence.owner == fixture.conditional.occurrence.owner)
            "Bool conditional cycle escaped its declaration"
      | _, _ => throw (IO.userError
          s!"Bool conditional cycle produced the wrong error: {reprStr error}")
  | result => throw (IO.userError
      s!"Bool conditional cycle produced the wrong result: {reprStr result}")

private structure WordFixture where
  function : CheckedFunction
  conditional : ExpressionId
  condition : ExpressionId
  thenBranch : ExpressionId

private def wordFixture : IO WordFixture := do
  let function ← checkedFunction
    "function words() returns (Word) { return wordFromInteger(wordToInteger(true ? 1 : 2)); }"
  let root ← returnedExpression function
  let conversion ← unaryBuiltinArgument function root .wordFromInteger
  let wordConditional ← unaryBuiltinArgument function conversion .wordToInteger
  let (condition, thenBranch, _) ← conditional function wordConditional
  pure { function, conditional := wordConditional, condition, thenBranch }

private def testWordCycle (fixture : WordFixture) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedWord
      fixture.function.solvedRequirements fixture.function.typedBody
      fixture.conditional with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = Core.Word.ofNatModulo 1 ∧
          evaluated.consumedRequirements =
            fixture.function.solvedRequirements.map (·.id)))
        "Word conditional baseline changed"
  | .error error => throw (IO.userError
      s!"Word conditional baseline failed: {reprStr error}")
  let cycle := withExpression fixture.function fixture.conditional fun node =>
    { node with form := match node.form with
      | .conditional condition _ elseBranch =>
          .conditional condition fixture.conditional elseBranch
      | form => form }
  match SourceCoreElaboration.evaluateStagedWord cycle.solvedRequirements
      cycle.typedBody fixture.conditional with
  | .error error =>
      match error.site, error.reason with
      | .occurrence occurrence, .stagedBoolDepthLimit =>
          assertTrue (occurrence.owner == fixture.conditional.occurrence.owner)
            "Word conditional cycle escaped its declaration"
      | _, _ => throw (IO.userError
          s!"Word conditional cycle produced the wrong error: {reprStr error}")
  | result => throw (IO.userError
      s!"Word conditional cycle produced the wrong result: {reprStr result}")

/-- Reject malformed selected and unselected conditional metadata before Core. -/
def testSourceStagedConditionalsTamper : IO Unit := do
  let integer ← integerFixture
  testIntegerBaselineAndParentMetadata integer
  testIntegerChildrenAndUnselectedValidation integer
  testIntegerAndConditionCycles integer
  let bool ← boolFixture
  testBoolMetadataSpellingAndCycle bool
  let word ← wordFixture
  testWordCycle word
  IO.println "staged conditional tamper checks GREEN"

end Tests.SourceStagedConditionalsTamper
end

section
-- leanmerge: from Solcore.Test.SourceStagedMarkedImplMethods
/-!
End-to-end boundaries for implementation methods whose validated trait
contract marks parameters or results as `comptime`.
-/

set_option autoImplicit false

namespace Tests.SourceStagedMarkedImplMethods

open Solcore Solcore.Frontend
open Solcore.Frontend.SourceProgramExecution

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | none => throw (IO.userError "invalid staged marked-method module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def limits : Limits := {
  checkingFuel := 2048
  specializationBudget := 12
  executionFuel := 4096
}

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def source : String := String.intercalate "\n" [
  "trait Add<T> {",
  "  function add(comptime left: T, comptime right: T) returns (comptime<T>);",
  "}",
  "impl Add<Word> {",
  "  function add(comptime left: Word, comptime right: Word)",
  "      returns (comptime<Word>) {",
  "    return 94;",
  "  }",
  "}",
  "trait Coerce<From, To> {",
  "  function coerce(comptime value: From) returns (comptime<To>);",
  "}",
  "impl Coerce<Bool, Word> {",
  "  function coerce(comptime value: Bool) returns (comptime<Word>) {",
  "    return value ? 93 : 92;",
  "  }",
  "}",
  "function stagedAdd<T>(comptime left: T, comptime right: T)",
  "    returns (comptime<T>) where T: Add {",
  "  return left + right;",
  "}",
  "function stagedFlag() returns (comptime<Bool>) { return true; }",
  "function stagedAddEntry() returns (Word) { return stagedAdd(5, 6); }",
  "function stagedCoerceEntry() returns (Word) { return stagedFlag(); }",
  "function runtimeAdd<T>(left: T, right: T) returns (T) where T: Add {",
  "  return left + right;",
  "}",
  "function runtimeAddEntry(left: Word, right: Word) returns (Word) {",
  "  return runtimeAdd(left, right);",
  "}",
  "function acceptWord(value: Word) returns (Word) { return value; }",
  "function runtimeCoerceEntry(value: Bool) returns (Word) {",
  "  return acceptWord(value);",
  "}"
]

private def prepareNamed (name : String) : IO PreparedEntry := do
  let moduleId ← mainModule
  match prepare (workspace source) (Seed.named moduleId name) limits with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError
      s!"{name}: staged marked-method preparation failed: {reprStr error}")

private def assertClosedWord (name : String) (expected : Nat) : IO Unit := do
  let prepared ← prepareNamed name
  let value := word expected
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .word value ∧
      prepared.entry.elaborated.core = .word value))
    s!"{name}: marked implementation result was not materialized exactly"
  let store : Core.Store := [
    .bool false,
    .word (word 71),
    .pair (.word (word 4)) (.bool true)
  ]
  assertTrue (decide (prepared.run? [] 4096 store =
      some (.done (.word value) store)))
    s!"{name}: marked implementation changed its result or caller store"

private def testMarkedMethodsExecuteOnlyWhenStaged : IO Unit := do
  assertClosedWord "stagedAddEntry" 94
  assertClosedWord "stagedCoerceEntry" 93

private def expectRuntimeRejection (name : String)
    (expectedParameters : List Bool) : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace source) (Seed.named moduleId name) limits with
  | .error (.linking (.detachedComptimeUnsupported _ parameters true)) =>
      assertTrue (parameters == expectedParameters)
        s!"{name}: runtime rejection lost the marked parameter contract"
  | result => throw (IO.userError
      s!"{name}: a marked method escaped through runtime linking: {reprStr result}")

private def testMarkedMethodsDoNotEscapeToRuntime : IO Unit := do
  expectRuntimeRejection "runtimeAddEntry" [true, true]
  expectRuntimeRejection "runtimeCoerceEntry" [true]

def testSourceStagedMarkedImplMethods : IO Unit := do
  testMarkedMethodsExecuteOnlyWhenStaged
  testMarkedMethodsDoNotEscapeToRuntime

end Tests.SourceStagedMarkedImplMethods
end

section
-- leanmerge: from Solcore.Test.SourceStagedRecursion
/-!
End-to-end regressions for fuel-bounded, selected-branch staged recursion.

These tests exercise both the dedicated staged-integer evaluator and the
general Core-representable staged-value evaluator through the public program
preparation boundary.  Successful cases must close to constants and preserve
the caller's store; divergent staged calls and ordinary runtime recursion keep
distinct errors. Runtime recursion uses the common public Core compiler and
a typed checkpoint; staging and runtime keep separate execution budgets.
-/

set_option autoImplicit false

namespace Tests.SourceStagedRecursion

open Solcore Solcore.Frontend
open Solcore.Frontend.SourceProgramExecution

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | none => throw (IO.userError "invalid staged-recursion module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def limits (specializationBudget stagingFuel : Nat) : Limits := {
  checkingFuel := 4096
  specializationBudget
  stagingFuel
  executionFuel := 4096
}

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def prepareNamed (label content root : String)
    (specializationBudget stagingFuel : Nat) : IO PreparedEntry := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId root)
      (limits specializationBudget stagingFuel) with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError
      s!"{label}: staged-recursion preparation failed: {reprStr error}")

private def preservedStore : Core.Store := [
  .bool false,
  .word (word 73),
  .pair (.word (word 4)) (.bool true)
]

private def assertClosedWord (label content root : String)
    (specializationBudget stagingFuel expected : Nat) : IO Unit := do
  let prepared ← prepareNamed label content root specializationBudget stagingFuel
  let expectedWord := word expected
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .word expectedWord ∧
      prepared.entry.elaborated.core = .word expectedWord))
    s!"{label}: staged recursion was not materialized as one Word constant"
  assertTrue (decide (prepared.run? [] 4096 preservedStore =
      some (.done (.word expectedWord) preservedStore)))
    s!"{label}: staged recursion changed its result or caller store"

private def assertClosedBool (label content root : String)
    (specializationBudget stagingFuel : Nat) (expected : Bool) : IO Unit := do
  let prepared ← prepareNamed label content root specializationBudget stagingFuel
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .bool expected ∧
      prepared.entry.elaborated.core = .bool expected))
    s!"{label}: staged recursion was not materialized as one Bool constant"
  assertTrue (decide (prepared.run? [] 4096 preservedStore =
      some (.done (.bool expected) preservedStore)))
    s!"{label}: staged recursion changed its result or caller store"

private def integerRecursionSource : String := String.intercalate "\n" [
  "function countdown(comptime n: integer) returns (comptime<integer>) {",
  "  return integerEq(n, 0) ? 0 : countdown(integerSub(n, 1));",
  "}",
  "function factorial(comptime n: integer) returns (comptime<integer>) {",
  "  return integerEq(n, 0) ? 1 :",
  "    integerMul(n, factorial(integerSub(n, 1)));",
  "}",
  "function fib(comptime n: integer) returns (comptime<integer>) {",
  "  return integerLt(n, 2) ? n :",
  "    integerAdd(fib(integerSub(n, 1)), fib(integerSub(n, 2)));",
  "}",
  "function left(comptime n: integer) returns (comptime<integer>) {",
  "  return integerEq(n, 0) ? 0 : right(integerSub(n, 1));",
  "}",
  "function right(comptime n: integer) returns (comptime<integer>) {",
  "  return integerEq(n, 0) ? 0 : left(integerSub(n, 1));",
  "}",
  "function countdownEntry() returns (Word) {",
  "  return wordFromInteger(countdown(5));",
  "}",
  "function factorialEntry() returns (Word) {",
  "  return wordFromInteger(factorial(5));",
  "}",
  "function fibEntry() returns (Word) {",
  "  return wordFromInteger(fib(10));",
  "}",
  "function mutualEntry() returns (Word) {",
  "  return wordFromInteger(left(6));",
  "}"
]

private def testIntegerRecursion : IO Unit := do
  assertClosedWord "integer countdown" integerRecursionSource
    "countdownEntry" 2 64 0
  assertClosedWord "integer factorial" integerRecursionSource
    "factorialEntry" 2 64 120
  assertClosedWord "integer Fibonacci" integerRecursionSource
    "fibEntry" 2 64 55
  assertClosedWord "integer mutual countdown" integerRecursionSource
    "mutualEntry" 3 64 0

private def generalRecursionSource : String := String.intercalate "\n" [
  "function finishWord(comptime value: Word, comptime stop: Bool)",
  "    returns (comptime<Word>) {",
  "  return stop ? value : finishWord(value, true);",
  "}",
  "function finishBool(comptime stop: Bool) returns (comptime<Bool>) {",
  "  return stop ? true : finishBool(true);",
  "}",
  "function finishStatement(comptime stop: Bool) returns (comptime<Word>) {",
  "  if (stop) {",
  "    return 9;",
  "  } else {",
  "    return finishStatement(true);",
  "  }",
  "}",
  "function wordEntry() returns (Word) {",
  "  return finishWord(7, false);",
  "}",
  "function boolEntry() returns (Bool) {",
  "  return finishBool(false);",
  "}",
  "function statementEntry() returns (Word) {",
  "  return finishStatement(false);",
  "}"
]

private def testGeneralWordAndBoolRecursion : IO Unit := do
  assertClosedWord "general Word/Bool recursion" generalRecursionSource
    "wordEntry" 2 16 7
  assertClosedBool "general Bool recursion" generalRecursionSource
    "boolEntry" 2 16 true
  assertClosedWord "general statement recursion" generalRecursionSource
    "statementEntry" 2 16 9

private def genericEvidenceRecursionSource : String := String.intercalate "\n" [
  "trait Marker<T> {}",
  "impl Marker<Word> {}",
  "function finish<T>(comptime value: T, comptime stop: Bool)",
  "    returns (comptime<T>) where T: Marker {",
  "  return stop ? value : finish(value, true);",
  "}",
  "function entry() returns (Word) { return finish(11, false); }"
]

private def testGenericEvidenceRecursion : IO Unit :=
  assertClosedWord "generic evidence recursion" genericEvidenceRecursionSource
    "entry" 2 16 11

private def unselectedFaultSource : String := String.intercalate "\n" [
  "function safe() returns (comptime<Word>) {",
  "  return true ? 7 : 1 / 0;",
  "}",
  "function entry() returns (Word) { return safe(); }"
]

private def testUnselectedFaultIsNotExecuted : IO Unit :=
  assertClosedWord "unselected staged fault" unselectedFaultSource
    "entry" 2 8 7

private def unselectedRecursiveBranchSource : String :=
  String.intercalate "\n" [
    "function constant(comptime value: Word) returns (comptime<Word>) {",
    "  return value;",
    "}",
    "function loop(comptime value: Word) returns (comptime<Word>) {",
    "  return loop(value);",
    "}",
    "function entry() returns (Word) {",
    "  return true ? constant(1) : loop(0);",
    "}"
  ]

private def testUnselectedInfiniteRecursionIsNotExecuted : IO Unit :=
  assertClosedWord "unselected infinite recursion"
    unselectedRecursiveBranchSource "entry" 3 8 1

private def expectStagedInvocationCycle (label content root : String)
    (specializationBudget stagingFuel : Nat) : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId root)
      (limits specializationBudget stagingFuel) with
  | .error (.linking (.stagedInvocationCycle _)) => pure ()
  | result => throw (IO.userError
      s!"{label}: expected a staged invocation cycle, got {reprStr result}")

private def selfCycleSource : String := String.intercalate "\n" [
  "function loop(comptime n: integer) returns (comptime<integer>) {",
  "  return loop(n);",
  "}",
  "function entry() returns (Word) { return wordFromInteger(loop(1)); }"
]

private def mutualCycleSource : String := String.intercalate "\n" [
  "function left(comptime value: Word) returns (comptime<Word>) {",
  "  return right(value);",
  "}",
  "function right(comptime value: Word) returns (comptime<Word>) {",
  "  return left(value);",
  "}",
  "function entry() returns (Word) { return left(1); }"
]

private def testSameValueCycles : IO Unit := do
  expectStagedInvocationCycle "same-value self recursion" selfCycleSource
    "entry" 2 16
  expectStagedInvocationCycle "same-value mutual recursion" mutualCycleSource
    "entry" 3 16

private def expectStagedFuelExhausted (label content root : String)
    (specializationBudget stagingFuel : Nat) : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId root)
      (limits specializationBudget stagingFuel) with
  | .error (.linking (.stagedFuelExhausted _)) => pure ()
  | result => throw (IO.userError
      s!"{label}: expected staged fuel exhaustion, got {reprStr result}")

private def increasingSource : String := String.intercalate "\n" [
  "function grow(comptime n: integer) returns (comptime<integer>) {",
  "  return grow(integerAdd(n, 1));",
  "}",
  "function entry() returns (Word) { return wordFromInteger(grow(0)); }"
]

private def testStagedFuelBoundaries : IO Unit := do
  expectStagedFuelExhausted "increasing staged nontermination"
    increasingSource "entry" 2 8
  expectStagedFuelExhausted "terminating recursion with insufficient fuel"
    integerRecursionSource "countdownEntry" 2 1

private def runtimeRecursionSource : String := String.intercalate "\n" [
  "function loop(value: Word) returns (Word) { return loop(value); }"
]

private def testRuntimeRecursionUsesExecutionFuel : IO Unit := do
  let moduleId ← mainModule
  let source ← SourceCompilerFeatureSupport.get "runtime recursion compilation"
    (SourceCoreCompiler.compile (workspace runtimeRecursionSource)
      [SourceCoreCompiler.Seed.named moduleId "loop"]
      {checkingFuel := 4096, specializationBudget := 1, compilationFuel := 1000})
  assertTrue (source.rootCount == 1 && source.plan.specializations.length == 1)
    "runtime recursion did not retain one Core specialization"
  let compiled ← SourceCompilerFeatureSupport.fromCompiled source
  let invoked ← compiled.invoke [.word (word 1)] {inputValidationFuel := 64, executionFuel := 200}
  match invoked.outcome with
  | .outOfFuel checkpoint =>
      assertTrue (checkpoint.heapSize > invoked.initial.heapSize)
        "runtime recursion did not retain its allocated parameter cells"
      match ← checkpoint.resume 200 with
      | .outOfFuel continued =>
          assertTrue (continued.heapSize ≥ checkpoint.heapSize)
            "resumed runtime recursion discarded allocated cells"
      | _ => throw (IO.userError "resumed runtime recursion unexpectedly terminated")
  | _ => throw (IO.userError "runtime recursion did not use the execution fuel boundary")

/-- Exercise staged and Core runtime recursion through their
independent public fuel boundaries. -/
def testSourceStagedRecursion : IO Unit := do
  testIntegerRecursion
  testGeneralWordAndBoolRecursion
  testGenericEvidenceRecursion
  testUnselectedFaultIsNotExecuted
  testUnselectedInfiniteRecursionIsNotExecuted
  testSameValueCycles
  testStagedFuelBoundaries
  testRuntimeRecursionUsesExecutionFuel
  IO.println "staged recursion checks GREEN"

end Tests.SourceStagedRecursion
end

section
-- leanmerge: from Solcore.Test.SourceStagedRequiredOperators
/-!
End-to-end regressions for evidence-selected unary and binary operations in the
Core-representable staged-value domain.
-/

set_option autoImplicit false

namespace Tests.SourceStagedRequiredOperators

open Solcore Solcore.Frontend
open Solcore.Frontend.SourceProgramExecution

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | none => throw (IO.userError "invalid staged required-operator module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def limits : Limits := {
  checkingFuel := 2048
  specializationBudget := 12
  executionFuel := 4096
}

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def prepareNamed (content name : String) : IO PreparedEntry := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId name) limits with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError
      s!"{name}: staged required-operator preparation failed: {reprStr error}")

private def assertClosedResult (content name : String)
    (expected : SourceStagedValue.Value) : IO Unit := do
  let prepared ← prepareNamed content name
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved =
        SourceStagedValue.toResolved expected ∧
      prepared.entry.elaborated.core = SourceStagedValue.toCoreExpr expected))
    s!"{name}: staged required operation was not materialized exactly"
  let store : Core.Store := [
    .bool true,
    .word (word 73),
    .pair (.word (word 4)) (.bool false)
  ]
  assertTrue (decide (prepared.run? [] 4096 store =
      some (.done (SourceStagedValue.toCore expected) store)))
    s!"{name}: staged required operation changed its result or store"

private def evidenceSource : String := String.intercalate "\n" [
  "trait Eq<T> {",
  "  function eq(left: T, right: T) returns (Bool);",
  "}",
  "trait Add<T> {",
  "  function add(left: T, right: T) returns (T) where T: Eq;",
  "}",
  "trait BitNot<T> {",
  "  function bnot(value: T) returns (T);",
  "}",
  "impl Eq<Word> {",
  "  function eq(left: Word, right: Word) returns (Bool) { return false; }",
  "}",
  "function equalWithEvidence<T>(left: T, right: T) returns (Bool)",
  "    where T: Eq {",
  "  return left == right;",
  "}",
  "impl Add<Word> {",
  "  function add(left: Word, right: Word) returns (Word) where Word: Eq {",
  "    return equalWithEvidence(left, right) ? 91 : 92;",
  "  }",
  "}",
  "impl BitNot<Word> {",
  "  function bnot(value: Word) returns (Word) { return 94; }",
  "}",
  "function stagedAdd<T>(comptime left: T, comptime right: T)",
  "    returns (comptime<T>) where T: Add, T: Eq {",
  "  return left + right;",
  "}",
  "function relayAdd<T>(comptime left: T, comptime right: T)",
  "    returns (comptime<T>) where T: Add, T: Eq {",
  "  return stagedAdd(left, right);",
  "}",
  "function stagedBitNot<T>(comptime value: T) returns (comptime<T>)",
  "    where T: BitNot {",
  "  return ~value;",
  "}",
  "function addEntry() returns (Word) { return relayAdd(5, 5); }",
  "function bitNotEntry() returns (Word) { return stagedBitNot(7); }"
]

private def testSelectedImplementationMethods : IO Unit := do
  assertClosedResult evidenceSource "addEntry" (.word (word 92))
  assertClosedResult evidenceSource "bitNotEntry" (.word (word 94))

private def builtinSource : String := String.intercalate "\n" [
  "function builtins(comptime left: Word, comptime right: Word)",
  "    returns (comptime<(Word, Word)>) {",
  "  return (left + right, ~left);",
  "}",
  "function builtinEntry() returns ((Word, Word)) {",
  "  return builtins(5, 6);",
  "}"
]

private def testRequirementFreeBuiltinCompatibility : IO Unit := do
  assertClosedResult builtinSource "builtinEntry"
    (.product (.word (word 11)) (.word (word 5).bitNot))

def testSourceStagedRequiredOperators : IO Unit := do
  testSelectedImplementationMethods
  testRequirementFreeBuiltinCompatibility

end Tests.SourceStagedRequiredOperators
end

section
-- leanmerge: from Solcore.Test.SourceStagedValueCalls
/-!
Whole-program regressions for Core-representable staged-value calls.

These cases enter only through the public source-program preparation and
execution boundary.  A successful case therefore checks source typing,
specialization discovery, direct linking, staged evaluation, Core reification,
and runtime execution together.
-/

set_option autoImplicit false

namespace Tests.SourceStagedValueCalls

open Solcore Solcore.Frontend
open Solcore.Frontend.SourceProgramExecution

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | none => throw (IO.userError "invalid staged-value call module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def limits (specializationBudget : Nat) : Limits := {
  checkingFuel := 1024
  specializationBudget
  executionFuel := 4096
}

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def positiveSource : String := String.intercalate "\n" [
  "function bump(comptime value: Word) returns (comptime<Word>) {",
  "  let alias: Word = (value);",
  "  return alias + 1;",
  "}",
  "function negate(comptime flag: Bool) returns (comptime<Bool>) {",
  "  return !flag;",
  "}",
  "function stagedUnit() returns (comptime<()>) { return; }",
  "function bundle(comptime value: Word, comptime flag: Bool) returns (comptime<(Word, Bool, ())>) {",
  "  let next: Word = bump(value);",
  "  return (next, negate(flag), stagedUnit());",
  "}",
  "function relay(value: Word) returns (comptime<Word>) {",
  "  let alias: Word = bump(value);",
  "  return bump(alias);",
  "}",
  "function entryWord() returns (Word) { return bump(41); }",
  "function entryBool() returns (Bool) { return negate(false); }",
  "function entryUnit() returns (()) { return stagedUnit(); }",
  "function entryProduct() returns ((Word, Bool, ())) {",
  "  return bundle(6, true);",
  "}",
  "function entryNested() returns (Word) { return relay(5); }",
  "function entryResultAlias() returns (Word) {",
  "  let alias: Word = relay(5);",
  "  return alias;",
  "}",
  "function entryAlias() returns (Word) {",
  "  let closed: Word = 8;",
  "  return relay(closed);",
  "}"
]

private def prepareNamed (content name : String) (budget : Nat) :
    IO PreparedEntry := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId name) (limits budget) with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError
      s!"{name}: staged-value call preparation failed: {reprStr error}")

private def assertPreparedClosed (name : String)
    (expected : SourceStagedValue.Value) : IO Unit := do
  let prepared ← prepareNamed positiveSource name 8
  let expectedValue := SourceStagedValue.toCore expected
  let expectedResolved := SourceStagedValue.toResolved expected
  let expectedCore := SourceStagedValue.toCoreExpr expected
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = expectedResolved ∧
      prepared.entry.elaborated.core = expectedCore))
    s!"{name}: marked result was not reified as the exact closed Core value"
  let store : Core.Store := [
    .bool false,
    .word (word 77),
    .pair (.word (word 3)) (.bool true)
  ]
  assertTrue (decide (prepared.run? [] 4096 store =
      some (.done expectedValue store)))
    s!"{name}: prepared execution changed its value or store"
  let moduleId ← mainModule
  match SourceProgramExecution.run (workspace positiveSource)
      (Seed.named moduleId name) [] (limits 8) store with
  | .ok result =>
      assertTrue (decide (result = .done expectedValue store))
        s!"{name}: public run disagreed with the prepared entry"
  | .error error => throw (IO.userError
      s!"{name}: public staged-value execution failed: {reprStr error}")

private def testClosedResults : IO Unit := do
  assertPreparedClosed "entryWord" (.word (word 42))
  assertPreparedClosed "entryBool" (.bool true)
  assertPreparedClosed "entryUnit" .unit
  assertPreparedClosed "entryProduct"
    (.product (.word (word 7)) (.product (.bool false) .unit))
  assertPreparedClosed "entryNested" (.word (word 7))

private def testRuntimeCallerAlias : IO Unit := do
  let resultAlias ← prepareNamed positiveSource "entryResultAlias" 8
  let seven := word 7
  match resultAlias.entry.elaborated.resolved with
  | .letE binder (.word value) (.var reference) =>
      assertTrue (decide (binder = reference ∧ value = seven))
        "runtime result alias did not retain a closed staged initializer"
  | resolved => throw (IO.userError
      s!"runtime result alias has the wrong resolved shape: {reprStr resolved}")
  assertTrue (decide (resultAlias.run? [] 4096 =
      some (.done (.word seven) [])))
    "runtime result alias did not execute to the staged value"

  let prepared ← prepareNamed positiveSource "entryAlias" 8
  let expected := Core.Value.word (word 10)
  let store : Core.Store := [.word (word 91), .bool true]
  assertTrue (prepared.inputTypes.isEmpty)
    "entryAlias unexpectedly retained a runtime input"
  assertTrue (decide (prepared.run? [] 4096 store =
      some (.done expected store)))
    "a comptime-classified caller let alias did not cross nested marked calls"
  let moduleId ← mainModule
  match SourceProgramExecution.run (workspace positiveSource)
      (Seed.named moduleId "entryAlias") [] (limits 8) store with
  | .ok result =>
      assertTrue (decide (result = .done expected store))
        "public execution changed the caller-alias result"
  | .error error => throw (IO.userError
      s!"entryAlias: public execution failed: {reprStr error}")

private def boundarySource : String := String.intercalate "\n" [
  "function identity(comptime value: Word) returns (comptime<Word>) {",
  "  return value;",
  "}",
  "function producer(value: Word) returns (Word) { return value; }",
  "function runtimeAlias(value: Word) returns (Word) {",
  "  let alias: Word = value;",
  "  return identity(alias);",
  "}",
  "function deferredAlias(value: Word) returns (Word) {",
  "  let alias: Word = producer(value);",
  "  return identity(alias);",
  "}"
]

private def testRuntimeArgumentRejected : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace boundarySource)
      (Seed.named moduleId "runtimeAlias") (limits 3) with
  | .error (.linking (.runtimeArgumentToComptimeParameter _ _ 0 _)) =>
      pure ()
  | result => throw (IO.userError
      s!"runtime-dependent alias crossed a comptime parameter: {reprStr result}")

private def testDeferredArgumentRejected : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace boundarySource)
      (Seed.named moduleId "deferredAlias") (limits 4) with
  | .error (.linking (.comptimeArgumentDeferred _ _ 0 _)) => pure ()
  | result => throw (IO.userError
      s!"deferred alias crossed a comptime parameter: {reprStr result}")

/-- Exercise general staged direct calls through the public source-program
pipeline, including nested calls and caller-local stage propagation. -/
def testSourceStagedValueCalls : IO Unit := do
  testClosedResults
  testRuntimeCallerAlias
  testRuntimeArgumentRejected
  testDeferredArgumentRejected

end Tests.SourceStagedValueCalls
end

section
-- leanmerge: from Solcore.Test.SourceStagedValueCallsTamper
/-!
Whole-program rejection and resource-boundary regressions for direct
Core-representable staged calls.

Unlike the carrier-level tamper suite, these cases use only checked source and
the public preparation boundary.  They fix which unsupported call features
fail explicitly and ensure finite specialization does not make recursive
staged evaluation appear executable.
-/

set_option autoImplicit false

namespace Tests.SourceStagedValueCallsTamper

open Solcore Solcore.Frontend
open Solcore.Frontend.SourceProgramExecution

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | none => throw (IO.userError
      "invalid staged-value call boundary module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def limits (specializationBudget : Nat) : Limits := {
  checkingFuel := 1024
  specializationBudget
  executionFuel := 4096
}

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def predicateSource : String := String.intercalate "\n" [
  "trait Marker<T> {}",
  "impl Marker<Word> {}",
  "function marked<T>(comptime value: T) returns (comptime<T>) where T: Marker {",
  "  return value;",
  "}",
  "function relay<T>(comptime value: T) returns (comptime<T>) where T: Marker {",
  "  return marked(value);",
  "}",
  "function wrapper(comptime value: Word) returns (Word) where Word: Marker {",
  "  return relay(value);",
  "}",
  "function entry() returns (Word) { return wrapper(3); }"
]

private def testPredicateEvidenceForwarded : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace predicateSource)
      (Seed.named moduleId "entry") (limits 4) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"predicate-bearing marked calls failed: {reprStr error}")
  let store : Core.Store := [.bool false, .word (word 29)]
  assertTrue (decide (prepared.run? [] 4096 store =
      some (.done (.word (word 3)) store)))
    "proof-only staged call evidence changed the value or store"
  match prepared.entry.elaborated.resolved with
  | .letE temporary (.word argument)
      (.letE _ (.var reference) (.word result)) =>
      assertTrue (decide (temporary = reference ∧ argument = word 3 ∧
          result = word 3))
        "predicate-bearing nested staged result was not materialized"
  | resolved => throw (IO.userError
      s!"predicate-bearing staged calls have the wrong shape: {reprStr resolved}")

private def coercionSource : String := String.intercalate "\n" [
  "trait Coerce<From, To> {",
  "  function coerce(value: From) returns (To);",
  "}",
  "impl Coerce<Bool, Word> {",
  "  function coerce(value: Bool) returns (Word) {",
  "    return value ? 41 : 7;",
  "  }",
  "}",
  "function staged() returns (comptime<Bool>) { return true; }",
  "function entry() returns (Word) { return staged(); }"
]

private def testResultCoercionExecuted : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace coercionSource)
      (Seed.named moduleId "entry") (limits 2) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"marked result coercion failed: {reprStr error}")
  let store : Core.Store := [.bool false, .word (word 29)]
  assertTrue (decide (prepared.entry.elaborated.resolved = .word (word 41) ∧
      prepared.run? [] 4096 store =
        some (.done (.word (word 41)) store)))
    "marked result coercion was not staged or changed the store"

private def argumentAndResultCoercionSource : String := String.intercalate "\n" [
  "trait Coerce<From, To> {",
  "  function coerce(value: From) returns (To);",
  "}",
  "impl Coerce<Bool, Word> {",
  "  function coerce(value: Bool) returns (Word) {",
  "    return value ? 41 : 7;",
  "  }",
  "}",
  "function stagedFlag(comptime value: Word) returns (comptime<Bool>) {",
  "  return false;",
  "}",
  "function entry() returns (Word) { return stagedFlag(true); }"
]

private def testArgumentAndResultCoercions : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace argumentAndResultCoercionSource)
      (Seed.named moduleId "entry") (limits 2) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"staged argument/result coercions failed: {reprStr error}")
  let store : Core.Store := [.word (word 17), .bool true]
  assertTrue (decide (prepared.entry.elaborated.resolved = .word (word 7) ∧
      prepared.run? [] 4096 store = some (.done (.word (word 7)) store)))
    "argument/result coercion composition produced the wrong value or store"

private def genericCoercionSource : String := String.intercalate "\n" [
  "trait Coerce<From, To> {",
  "  function coerce(value: From) returns (To);",
  "}",
  "impl Coerce<Bool, Word> {",
  "  function coerce(value: Bool) returns (Word) {",
  "    return value ? 41 : 7;",
  "  }",
  "}",
  "function convert<T>(comptime value: T) returns (comptime<Word>)",
  "    where T: Coerce<Word> {",
  "  return value;",
  "}",
  "function relay<T>(comptime value: T) returns (comptime<Word>)",
  "    where T: Coerce<Word> {",
  "  return convert(value);",
  "}",
  "function entry() returns (Word) { return relay(true); }"
]

private def testGenericCoercionEvidenceForwarded : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace genericCoercionSource)
      (Seed.named moduleId "entry") (limits 3) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"generic staged coercion evidence failed: {reprStr error}")
  let store : Core.Store := [.bool false, .word (word 23)]
  assertTrue (decide (prepared.entry.elaborated.resolved = .word (word 41) ∧
      prepared.run? [] 4096 store =
        some (.done (.word (word 41)) store)))
    "generic coercion evidence was not forwarded through the staged call"

private def expectStagedCycle (label content root : String)
    (budget : Nat) : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId root)
      (limits budget) with
  | .error (.linking (.stagedInvocationCycle _)) => pure ()
  | result => throw (IO.userError
      s!"{label}: recursive staged call was not rejected: {reprStr result}")

private def selfRecursiveSource : String := String.intercalate "\n" [
  "function loop(comptime value: Word) returns (comptime<Word>) {",
  "  return loop(value);",
  "}",
  "function entry() returns (Word) { return loop(1); }"
]

private def mutualRecursiveSource : String := String.intercalate "\n" [
  "function left(comptime value: Word) returns (comptime<Word>) {",
  "  return right(value);",
  "}",
  "function right(comptime value: Word) returns (comptime<Word>) {",
  "  return left(value);",
  "}",
  "function entry() returns (Word) { return left(1); }"
]

private def eagerRecursiveSource : String := String.intercalate "\n" [
  "function constant(comptime value: Word) returns (comptime<Word>) {",
  "  return value;",
  "}",
  "function loop(comptime value: Word) returns (comptime<Word>) {",
  "  return loop(value);",
  "}",
  "function entry() returns (Word) {",
  "  return true ? constant(1) : loop(0);",
  "}"
]

private def testRecursiveBoundaries : IO Unit := do
  expectStagedCycle "self recursion" selfRecursiveSource "entry" 2
  expectStagedCycle "mutual recursion" mutualRecursiveSource "entry" 3
  let moduleId ← mainModule
  let prepared ← match prepare (workspace eagerRecursiveSource)
      (Seed.named moduleId "entry") (limits 3) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"unselected staged recursion was executed: {reprStr error}")
  assertTrue (decide (prepared.run? [] 64 =
      some (.done (.word (word 1)) [])))
    "selected staged branch did not retain its value"

private def deepAcyclicSource : String := String.intercalate "\n" [
  "function leaf(comptime value: Word) returns (comptime<Word>) {",
  "  return value + 1;",
  "}",
  "function stepOne(value: Word) returns (comptime<Word>) {",
  "  return leaf(value) + 1;",
  "}",
  "function stepTwo(value: Word) returns (comptime<Word>) {",
  "  return stepOne(value) + 1;",
  "}",
  "function stepThree(value: Word) returns (comptime<Word>) {",
  "  return stepTwo(value) + 1;",
  "}",
  "function entry() returns (Word) { return stepThree(5); }"
]

private def testDeepAcyclicCall : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace deepAcyclicSource)
      (Seed.named moduleId "entry") (limits 5) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"deep acyclic staged calls failed with sufficient budget: {reprStr error}")
  let expectedWord := word 9
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .word expectedWord ∧
      prepared.entry.elaborated.core = .word expectedWord))
    "deep acyclic staged chain was not reified as one closed Word"
  let store : Core.Store := [.bool true, .word (word 37)]
  assertTrue (decide (prepared.run? [] 4096 store =
      some (.done (.word expectedWord) store)))
    "deep acyclic staged chain changed its value or store"

private def ordinaryEvidenceLetSource : String := String.intercalate "\n" [
  "trait Coerce<From, To> {",
  "  function coerce(value: From) returns (To);",
  "}",
  "impl Coerce<Bool, Word> {",
  "  function coerce(value: Bool) returns (Word) { return 91; }",
  "}",
  "function entry() returns (Word) {",
  "  let alias: Word = true;",
  "  return alias;",
  "}"
]

private def testOrdinaryEvidenceLetPreserved : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace ordinaryEvidenceLetSource)
      (Seed.named moduleId "entry") (limits 1) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"ordinary evidence-bearing let regressed: {reprStr error}")
  assertTrue (decide (prepared.run? [] 4096 =
      some (.done (.word (word 91)) [])))
    "general staged caching bypassed ordinary coercion evidence execution"

private def comptimeInputDraftSource : String := String.intercalate "\n" [
  "function staged() returns (comptime<Word>) { return 7; }",
  "function direct(comptime unused: Word) returns (Word) {",
  "  return staged();",
  "}",
  "function cached(comptime unused: Word) returns (Word) {",
  "  let closed: Word = staged();",
  "  return closed;",
  "}",
  "function entryDirect() returns (Word) { return direct(1); }",
  "function entryCached() returns (Word) { return cached(1); }"
]

private def testIndependentComptimeInputDraft : IO Unit := do
  let moduleId ← mainModule
  let store : Core.Store := [.bool false, .word (word 33)]
  for (name, cached) in [("entryDirect", false), ("entryCached", true)] do
    let prepared ← match prepare (workspace comptimeInputDraftSource)
        (Seed.named moduleId name) (limits 3) with
      | .ok prepared => pure prepared
      | .error error => throw (IO.userError
          s!"{name}: input-independent staged draft was rejected: {reprStr error}")
    assertTrue (decide (prepared.run? [] 4096 store =
        some (.done (.word (word 7)) store)))
      s!"{name}: input-independent staged draft changed its value or store"
    match prepared.entry.elaborated.resolved, cached with
    | .letE temporary (.word argument)
        (.letE _ (.var reference) (.word result)), false =>
        assertTrue (decide (temporary = reference ∧ argument = word 1 ∧
            result = word 7))
          "direct input-independent call did not reify its marked result"
    | .letE temporary (.word argument)
        (.letE _ (.var reference)
          (.letE closed (.word result) (.var closedReference))), true =>
        assertTrue (decide (temporary = reference ∧ closed = closedReference ∧
            argument = word 1 ∧ result = word 7))
          "cached input-independent call did not reify its let initializer"
    | resolved, _ => throw (IO.userError
        s!"{name}: unexpected resolved draft shape: {reprStr resolved}")

private def knownComptimeInputSource : String := String.intercalate "\n" [
  "function increment(comptime value: Word) returns (comptime<Word>) {",
  "  return value + 1;",
  "}",
  "function helper(comptime value: Word) returns (Word) {",
  "  return increment(value);",
  "}",
  "function entry() returns (Word) { return helper(7); }",
  "function entryAlias() returns (Word) {",
  "  let known: Word = 12;",
  "  return helper(known);",
  "}",
  "function entryPair() returns ((Word, Word)) {",
  "  return (helper(2), helper(9));",
  "}"
]

private def testKnownComptimeInputPropagation : IO Unit := do
  let moduleId ← mainModule
  let store : Core.Store := [.word (word 41), .bool true]
  let prepared ← match prepare (workspace knownComptimeInputSource)
      (Seed.named moduleId "entry") (limits 3) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"known comptime input did not reach its runtime draft: {reprStr error}")
  assertTrue (decide (prepared.run? [] 4096 store =
      some (.done (.word (word 8)) store)))
    "known comptime input produced the wrong staged result or changed the store"
  match prepared.entry.elaborated.resolved with
  | .letE temporary (.word argument)
      (.letE _ (.var reference) (.word result)) =>
      assertTrue (decide (temporary = reference ∧ argument = word 7 ∧
          result = word 8))
        "known comptime input was not materialized inside the callee draft"
  | resolved => throw (IO.userError
      s!"known comptime input has the wrong resolved shape: {reprStr resolved}")

  let pair ← match prepare (workspace knownComptimeInputSource)
      (Seed.named moduleId "entryPair") (limits 3) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"distinct known inputs failed to prepare: {reprStr error}")
  assertTrue (decide (pair.run? [] 4096 store = some (.done
      (.pair (.word (word 3)) (.word (word 10))) store)))
    "two call sites sharing one type specialization also shared a staged value"

  let alias ← match prepare (workspace knownComptimeInputSource)
      (Seed.named moduleId "entryAlias") (limits 3) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"caller-local known alias failed to prepare: {reprStr error}")
  assertTrue (decide (alias.inputTypes = [] ∧
      alias.run? [] 4096 store = some (.done (.word (word 13)) store)))
    "caller-local staged alias did not reach the runtime callee draft"

private def mixedKnownInputSource : String := String.intercalate "\n" [
  "function choose(comptime flag: Bool) returns (comptime<Word>) {",
  "  return flag ? 2 : 9;",
  "}",
  "function helper(comptime flag: Bool, value: Word, select: Bool) returns (Word) {",
  "  let selected: Word = choose(flag);",
  "  return select ? selected : value;",
  "}",
  "function entry(value: Word, select: Bool) returns (Word) {",
  "  return helper(true, value, select);",
  "}"
]

private def testMixedKnownAndRuntimeInputs : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace mixedKnownInputSource)
      (Seed.named moduleId "entry") (limits 3) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"mixed staged/runtime inputs failed to prepare: {reprStr error}")
  assertTrue (decide (prepared.inputTypes = [.word, .bool]))
    "runtime arguments disappeared from the linked Core input context"
  let store : Core.Store := [.bool false, .word (word 77)]
  assertTrue (decide (prepared.run? [.word (word 40), .bool true] 4096 store =
      some (.done (.word (word 2)) store)))
    "known Bool input did not materialize the selected marked value"
  assertTrue (decide (prepared.run? [.word (word 40), .bool false] 4096 store =
      some (.done (.word (word 40)) store)))
    "runtime Word or Bool input was erased while propagating staged knowledge"

private def productKnownInputSource : String := String.intercalate "\n" [
  "function stagedProduct(comptime value: (Word, Bool)) returns (comptime<(Word, Bool)>) {",
  "  return value;",
  "}",
  "function helper(comptime value: (Word, Bool)) returns ((Word, Bool)) {",
  "  return stagedProduct(value);",
  "}",
  "function entry() returns ((Word, Bool)) {",
  "  return helper((4, true));",
  "}"
]

private def testProductKnownInput : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace productKnownInputSource)
      (Seed.named moduleId "entry") (limits 3) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"known product input failed to prepare: {reprStr error}")
  let expected := Core.Value.pair (.word (word 4)) (.bool true)
  let store : Core.Store := [.word (word 19)]
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.run? [] 4096 store = some (.done expected store)))
    "known product input did not retain its staged structure or store"
  match prepared.entry.elaborated.resolved with
  | .letE temporary (.pair (.word argumentWord) (.bool argumentFlag))
      (.letE _ (.var reference)
        (.pair (.word resultWord) (.bool resultFlag))) =>
      assertTrue (decide (temporary = reference ∧
          argumentWord = word 4 ∧ argumentFlag ∧
          resultWord = word 4 ∧ resultFlag))
        "product-valued marked result was not reified inside the runtime draft"
  | resolved => throw (IO.userError
      s!"known product input has the wrong resolved shape: {reprStr resolved}")

private def unavailableKnownInputSource : String := String.intercalate "\n" [
  "function identity(comptime value: Word) returns (comptime<Word>) {",
  "  return value;",
  "}",
  "function helper(comptime value: Word) returns (Word) {",
  "  return identity(value);",
  "}",
  "function producer(value: Word) returns (Word) { return value; }",
  "function runtimeEntry(value: Word) returns (Word) {",
  "  return helper(value);",
  "}",
  "function deferredEntry(value: Word) returns (Word) {",
  "  return helper(producer(value));",
  "}"
]

private def testUnavailableKnownInputsRejected : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace unavailableKnownInputSource)
      (Seed.named moduleId "runtimeEntry") (limits 3) with
  | .error (.linking (.runtimeArgumentToComptimeParameter _ _ 0 _)) =>
      pure ()
  | result => throw (IO.userError
      s!"runtime actual was promoted to a known comptime input: {reprStr result}")
  match prepare (workspace unavailableKnownInputSource)
      (Seed.named moduleId "deferredEntry") (limits 4) with
  | .error (.linking (.comptimeArgumentDeferred _ _ 0 _)) => pure ()
  | result => throw (IO.userError
      s!"deferred actual was promoted to a known comptime input: {reprStr result}")

/-- Fix proof-only evidence forwarding, staged coercion execution, exact
staged-cycle rejection, selected-branch recursion, ordinary evidence-let
compatibility, known/unavailable runtime-draft staging, mixed runtime inputs,
structural values, and successful finite evaluation of a sufficiently
budgeted acyclic chain. -/
def testSourceStagedValueCallsTamper : IO Unit := do
  testPredicateEvidenceForwarded
  testResultCoercionExecuted
  testArgumentAndResultCoercions
  testGenericCoercionEvidenceForwarded
  testRecursiveBoundaries
  testDeepAcyclicCall
  testOrdinaryEvidenceLetPreserved
  testIndependentComptimeInputDraft
  testKnownComptimeInputPropagation
  testMixedKnownAndRuntimeInputs
  testProductKnownInput
  testUnavailableKnownInputsRejected

end Tests.SourceStagedValueCallsTamper
end

section
-- leanmerge: from Solcore.Test.SourceStagedValues
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
    "terminal block/if or selected-branch execution changed"

private def testBranchRequirementAccounting (program : CheckedProgram) : IO Unit := do
  let specialized ← specializedNamed program "eagerProduct"
  let expression ← returnedExpression specialized
  let evaluated ← match SourceCoreElaboration.evaluateStagedValue
      specialized.stageAnalysis specialized.function.solvedRequirements
      specialized.function.typedBody expression with
    | .ok evaluated => pure evaluated
    | .error error => throw (IO.userError
        s!"branch-accounting product expression failed: {reprStr error}")
  let expectedRequirements :=
    specialized.function.solvedRequirements.map fun requirement => requirement.id
  let expectedValue := SourceStagedValue.Value.product (.word (word 1))
    (.product (.bool true) .unit)
  assertTrue (expectedRequirements.length == 2 &&
      evaluated.value == expectedValue &&
      evaluated.consumedRequirements == expectedRequirements)
    "unselected tuple branch was not validated in ledger order"
  let functionValue ← evaluateFunctionOrThrow "branch-accounting product"
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
  testBranchRequirementAccounting program
  testStageBoundaries program
  testArgumentBoundaries program

end Tests.SourceStagedValues
end

section
-- leanmerge: from Solcore.Test.SourceStagedValuesTamper
/-!
Adversarial regressions for the specialization and evaluation boundaries of
ADR-0358.  These tests deliberately forge otherwise inaccessible carrier
states and require the public evaluator to reject them deterministically.
-/

set_option autoImplicit false

namespace Tests.SourceStagedValuesTamper

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
  "function stagedPair(comptime left: Word, comptime right: Word) returns (comptime<Word>) {",
  "  return left + right;",
  "}",
  "function stagedChoice() returns (comptime<Word>) {",
  "  return true ? 1 : 2;",
  "}",
  "function stagedIdentity(comptime value: Word) returns (comptime<Word>) {",
  "  return value;",
  "}",
  "function stagedCaller() returns (comptime<Word>) {",
  "  return stagedIdentity(1);",
  "}",
  "function unrelated() returns (comptime<Word>) { return 3; }"
]

private def checkedProgram : IO CheckedProgram := do
  match checkProgram (workspace fixtureSource) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"staged-value tamper fixture failed checking: {reprStr errors}")

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
  match SourceSpecialization.specializeFunction signature function [] with
  | .ok specialized => pure specialized
  | .error error => throw (IO.userError
      s!"{name}: specialization failed: {reprStr error}")

private def word (value : Nat) : SourceStagedValue.Value :=
  .word (Core.Word.ofNatModulo value)

private def returnedExpression
    (specialized : SourceSpecialization.SpecializedFunction) :
    IO ExpressionId :=
  match specialized.function.typedBody.roots with
  | [.statement statement] =>
      match specialized.function.typedBody.lookupStatement? statement with
      | some { form := .returnStmt (some expression), .. } => pure expression
      | _ => throw (IO.userError "expected one valued return root")
  | roots => throw (IO.userError
      s!"expected one statement root, found {roots.length}")

private def testForgedAnalysisRejected (program : CheckedProgram) : IO Unit := do
  let specialized ← specializedNamed program "stagedPair"
  let returned ← returnedExpression specialized
  let forgedAnalysis : SourceStageAnalysis.Analysis := {
    specialized.stageAnalysis with
    expressions := specialized.stageAnalysis.expressions.filter fun entry =>
      entry.expression != returned
  }
  let forged := { specialized with stageAnalysis := forgedAnalysis }
  match SourceCoreElaboration.evaluateStagedValueFunction forged [word 1, word 2] with
  | .ok value => throw (IO.userError
      s!"forged stage analysis evaluated to {reprStr value}")
  | .error error =>
      match error.reason with
      | .stagedValueAnalysisMismatch expected actual =>
          assertTrue (decide (error.site = .declaration specialized.declaration ∧
              expected = specialized.stageAnalysis ∧ actual = forgedAnalysis))
            s!"wrong forged-analysis diagnostic: {reprStr error}"
      | reason => throw (IO.userError
          s!"expected stagedValueAnalysisMismatch, found {reprStr reason}")

private def testForgedKeyRejected (program : CheckedProgram) : IO Unit := do
  let specialized ← specializedNamed program "stagedPair"
  let (unrelated, _) ← checkedNamed program "unrelated"
  let forged := {
    specialized with
    key := { specialized.key with declaration := unrelated.id }
  }
  match SourceCoreElaboration.evaluateStagedValueFunction forged [word 1, word 2] with
  | .ok value => throw (IO.userError
      s!"forged specialization key evaluated to {reprStr value}")
  | .error error =>
      assertTrue (decide (error.site = .declaration specialized.declaration ∧
          error.reason = .stagedValueSpecializationKeyMismatch
            specialized.declaration unrelated.id))
        s!"wrong forged-key diagnostic: {reprStr error}"

private def testTotalArityReported (program : CheckedProgram) : IO Unit := do
  let specialized ← specializedNamed program "stagedPair"
  for (arguments, actual) in [([word 1], 1), ([word 1, word 2, word 3], 3)] do
    match SourceCoreElaboration.evaluateStagedValueFunction specialized arguments with
    | .ok value => throw (IO.userError
        s!"arity {actual} unexpectedly evaluated to {reprStr value}")
    | .error error =>
        assertTrue (decide (error.site = .declaration specialized.declaration ∧
            error.reason = .stagedValueArgumentArityMismatch 2 actual))
          s!"wrong total-arity diagnostic for {actual}: {reprStr error}"

private def replaceExpression (source : TypedSource) (target : ExpressionId)
    (replace : ExpressionNode → ExpressionNode) : TypedSource := {
  source with
  nodes := source.nodes.map fun
    | .expression node =>
        if node.id = target then .expression (replace node)
        else .expression node
    | .statement node => .statement node
}

private def testGuardTypePrecedesBranchStage
    (program : CheckedProgram) : IO Unit := do
  let specialized ← specializedNamed program "stagedChoice"
  let conditional ← returnedExpression specialized
  let source := specialized.function.typedBody
  let (condition, thenBranch) ←
    match source.lookupExpression? conditional with
    | some { form := .conditional condition thenBranch _, .. } =>
        pure (condition, thenBranch)
    | _ => throw (IO.userError "expected a conditional return expression")
  let forgedSource := replaceExpression source condition fun node => {
    node with
    type := .word
    form := .literal (.decimal "0")
    requirements := []
    coercions := []
  }
  let forgedAnalysis : SourceStageAnalysis.Analysis := {
    specialized.stageAnalysis with
    expressions := specialized.stageAnalysis.expressions.filter fun entry =>
      entry.expression != thenBranch
  }
  match SourceCoreElaboration.evaluateStagedValue forgedAnalysis
      specialized.function.solvedRequirements forgedSource conditional with
  | .ok evaluated => throw (IO.userError
      s!"non-Bool conditional guard evaluated to {reprStr evaluated}")
  | .error error =>
      assertTrue (decide (error.site = .occurrence conditional.occurrence ∧
          error.reason = .stagedValueTypeMismatch .bool .word))
        s!"branch-stage error preceded guard-type error: {reprStr error}"

private def evaluateCallerWith
    (specialized : SourceSpecialization.SpecializedFunction)
    (plan : SourceCoreElaboration.StagedValueCallPlan
      SourceCoreElaboration.Error) :
    Except SourceCoreElaboration.Error SourceStagedValue.Value :=
  SourceCoreElaboration.evaluateStagedValueFunctionWith
    (fun error => error) (fun _ _ _ _ => pure plan) specialized []

private def testCallPolicyValidation (program : CheckedProgram) : IO Unit := do
  let specialized ← specializedNamed program "stagedCaller"
  let call ← returnedExpression specialized
  let valid : SourceCoreElaboration.StagedValueCallPlan
      SourceCoreElaboration.Error := {
    argumentTypes := [.word]
    resultType := .word
    consumedRequirements := []
    invoke := fun
      | [.word value] => pure (.word value)
      | values => .error {
          site := .occurrence call.occurrence
          reason := .stagedValueArgumentArityMismatch 1 values.length
        }
  }
  match evaluateCallerWith specialized valid with
  | .ok (.word value) =>
      assertTrue (value == Core.Word.ofNatModulo 1)
        "valid staged call policy changed its argument value"
  | result => throw (IO.userError
      s!"valid staged call policy failed: {reprStr result}")

  let wrongRequirements := {
    valid with consumedRequirements := [{ index := 999 }]
  }
  match evaluateCallerWith specialized wrongRequirements with
  | .error error =>
      assertTrue (decide (error.site = .occurrence call.occurrence ∧
          error.reason = .stagedValueCallRequirementsMismatch []
            [{ index := 999 }]))
        s!"wrong staged call requirement diagnostic: {reprStr error}"
  | result => throw (IO.userError
      s!"staged call accepted forged requirements: {reprStr result}")

  let wrongArity := { valid with argumentTypes := [] }
  match evaluateCallerWith specialized wrongArity with
  | .error error =>
      assertTrue (decide (error.site = .occurrence call.occurrence ∧
          error.reason = .stagedValueCallArgumentArityMismatch 0 1))
        s!"wrong staged call plan-arity diagnostic: {reprStr error}"
  | result => throw (IO.userError
      s!"staged call accepted a forged plan arity: {reprStr result}")

  let wrongResultType := { valid with resultType := .bool }
  match evaluateCallerWith specialized wrongResultType with
  | .error error =>
      assertTrue (decide (error.site = .occurrence call.occurrence ∧
          error.reason = .stagedValueCallResultTypeMismatch .word .bool))
        s!"wrong staged call result-plan diagnostic: {reprStr error}"
  | result => throw (IO.userError
      s!"staged call accepted a forged result type: {reprStr result}")

  let wrongValue := { valid with invoke := fun _ => pure (.bool true) }
  match evaluateCallerWith specialized wrongValue with
  | .error error =>
      assertTrue (decide (error.site = .occurrence call.occurrence ∧
          error.reason = .stagedValueTypeMismatch .word .bool))
        s!"wrong staged call result-value diagnostic: {reprStr error}"
  | result => throw (IO.userError
      s!"staged call accepted a forged result value: {reprStr result}")

/-- Fix the defensive ADR-0358 rejection and validation-order boundaries. -/
def testSourceStagedValuesTamper : IO Unit := do
  let program ← checkedProgram
  testForgedAnalysisRejected program
  testForgedKeyRejected program
  testTotalArityReported program
  testGuardTypePrecedesBranchStage program
  testCallPolicyValidation program

end Tests.SourceStagedValuesTamper
end
