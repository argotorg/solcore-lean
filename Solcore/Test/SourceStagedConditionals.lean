import Solcore

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
