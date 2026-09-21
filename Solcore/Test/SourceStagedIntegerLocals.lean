import Solcore

/-! End-to-end regressions for eager, let-bound staged integers. -/

set_option autoImplicit false

namespace Tests.SourceStagedIntegerLocals

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
  | none => throw (IO.userError "invalid staged-local module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"staged-local fixture failed checking: {reprStr errors}")

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

private def statementRoots (function : CheckedFunction) : IO (List StatementId) :=
  function.typedBody.roots.mapM fun
    | .statement statement => pure statement
    | .expression expression => throw (IO.userError
        s!"staged-local fixture retained expression root {reprStr expression}")

private def letBinding (function : CheckedFunction) (id : StatementId) :
    IO (TypedBinder × ExpressionId) :=
  match function.typedBody.lookupStatement? id with
  | some node =>
      match node.form with
      | .letDecl binder (some initializer) => do
          assertTrue (node.type == Ty.unit)
            "staged let statement lost Unit type"
          pure (binder, initializer)
      | _ => throw (IO.userError
          s!"expected initialized let statement, found {reprStr node}")
  | none => throw (IO.userError "staged let statement was absent")

private def returnedExpression (function : CheckedFunction)
    (id : StatementId) : IO ExpressionId :=
  match function.typedBody.lookupStatement? id with
  | some { form := .returnStmt (some expression), .. } => pure expression
  | node => throw (IO.userError
      s!"staged-local final statement is not a valued return: {reprStr node}")

private def builtinArguments (function : CheckedFunction) (id : ExpressionId)
    (expected : BuiltinFunctionId) : IO (List ExpressionId) :=
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .call callee arguments (.builtinFunction actual) => do
          let calleeValid := match function.typedBody.lookupExpression? callee with
            | some calleeNode =>
                match calleeNode.form with
                | .reference spelling (.builtinFunction identity) =>
                    identity == expected && spelling == expected.spelling &&
                      calleeNode.type == expected.type &&
                      calleeNode.requirements.isEmpty &&
                      calleeNode.coercions.isEmpty
                | _ => false
            | none => false
          assertTrue (actual == expected &&
              node.type == expected.returnType &&
              arguments.length == expected.parameterTypes.length &&
              node.requirements.isEmpty && node.coercions.isEmpty &&
              calleeValid)
            s!"builtin `{expected.spelling}` lost exact typed metadata"
          pure arguments
      | _ => throw (IO.userError
          s!"expected builtin `{expected.spelling}`, found {reprStr node}")
  | none => throw (IO.userError
      s!"builtin `{expected.spelling}` was absent")

private def localReference (function : CheckedFunction) (id : ExpressionId)
    (expected : TypedBinder) : IO Unit :=
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .reference name (.local binder) =>
          assertTrue (binder == expected.id && name == expected.name &&
              node.type == Ty.integer && node.requirements.isEmpty &&
              node.coercions.isEmpty)
            "staged local reference lost binder identity or empty metadata"
      | _ => throw (IO.userError
          s!"expected staged local reference, found {reprStr node}")
  | none => throw (IO.userError "staged local reference was absent")

private def integerLiteralRequirement (function : CheckedFunction)
    (id : ExpressionId) (expected : Nat) : IO RequirementId :=
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .integerLiteral _ resolution => do
          assertTrue (node.type == Ty.integer &&
              resolution.targetType == Ty.integer &&
              resolution.rawValue == expected &&
              node.requirements == [resolution.requirement] &&
              node.coercions.isEmpty)
            "staged-local literal lost integer target or exact requirement"
          pure resolution.requirement
      | _ => throw (IO.userError
          s!"expected staged integer literal, found {reprStr node}")
  | none => throw (IO.userError "staged integer literal was absent")

private def positiveSource : String := String.intercalate "\n" [
  "function basic() returns (Word) {",
  "  let x = 42;",
  "  let y = integerAdd(x, 8);",
  "  return wordFromInteger(integerMul(y, 2));",
  "}",
  "function negative() returns (Word) {",
  "  let x: integer = integerSub(0, 3);",
  "  let y: integer = integerMul(x, 5);",
  "  return wordFromInteger(y);",
  "}",
  "function reuse() returns (Word) {",
  "  let x: integer = integerSub(1, 2);",
  "  return wordFromInteger(integerAdd(x, x));",
  "}",
  "function shadow() returns (Word) {",
  "  let x: integer = 3;",
  "  let x: integer = integerAdd(x, 1);",
  "  return wordFromInteger(x);",
  "}",
  "function chain() returns (Word) {",
  "  let a: integer = 2;",
  "  let b: integer = integerMul(a, 3);",
  "  let c: integer = integerSub(b, 1);",
  "  return wordFromInteger(c);",
  "}",
  "function unused() returns (Word) {",
  "  let ignored: integer = integerAdd(20, 22);",
  "  return 7;",
  "}",
  "function composed() returns (Word) {",
  "  let base = integerSub(10, 3);",
  "  {",
  "    let chosen = integerLt(base, 8) ? integerAdd(base, 5) : wordToInteger(99);",
  "    return wordFromInteger(chosen);",
  "  }",
  "}",
  "function roundtripEq() returns (Word) {",
  "  let x = 5;",
  "  return integerEq(wordToInteger(wordFromInteger(x)), x) ? 1 : 0;",
  "}",
  "function runtimeWord(value: Word) returns (Word) {",
  "  let next: Word = value + 1;",
  "  return next * 2;",
  "}"
]

private def limits : Limits := {
  checkingFuel := 1024
  specializationBudget := 1
  executionFuel := 1024
}

private def testReferenceCarrier : IO Unit := do
  let program ← checkedProgram positiveSource
  let function ← checkedNamed program "basic"
  let roots ← statementRoots function
  let (xStatement, yStatement, returnStatement) ← match roots with
    | [x, y, result] => pure (x, y, result)
    | _ => throw (IO.userError
        s!"basic staged-local fixture retained {roots.length} roots")
  let (x, xInitializer) ← letBinding function xStatement
  let (y, yInitializer) ← letBinding function yStatement
  assertTrue (x.scheme == .mono Ty.integer &&
      y.scheme == .mono Ty.integer && x.id != y.id &&
      x.id.owner == function.declaration &&
      y.id.owner == function.declaration)
    "staged let binders lost monomorphic integer identity"
  let xRequirement ← integerLiteralRequirement function xInitializer 42
  let yArguments ← builtinArguments function yInitializer .integerAdd
  let (xReference, eight) ← match yArguments with
    | [reference, literal] => pure (reference, literal)
    | _ => throw (IO.userError "integerAdd lost its two operands")
  localReference function xReference x
  let eightRequirement ← integerLiteralRequirement function eight 8
  let returned ← returnedExpression function returnStatement
  let outer ← builtinArguments function returned .wordFromInteger
  let multiplication ← match outer with
    | [inner] => pure inner
    | _ => throw (IO.userError "wordFromInteger lost its argument")
  let multiplicationArguments ←
    builtinArguments function multiplication .integerMul
  let (yReference, two) ← match multiplicationArguments with
    | [reference, literal] => pure (reference, literal)
    | _ => throw (IO.userError "integerMul lost its two operands")
  localReference function yReference y
  let twoRequirement ← integerLiteralRequirement function two 2
  let expectedRequirements := [xRequirement, eightRequirement, twoRequirement]
  assertTrue (function.solvedRequirements.map (·.id) == expectedRequirements)
    "staged let initializer requirements changed source order or duplicated reads"
  match SourceCoreElaboration.evaluateStagedInteger
      function.solvedRequirements function.typedBody yInitializer with
  | .error error =>
      assertTrue (decide (error.site = .occurrence xReference.occurrence) &&
          error.reason == .unknownLocal x.id)
        s!"public staged evaluator did not preserve its empty-local boundary: {reprStr error}"
  | .ok evaluated => throw (IO.userError
      s!"public staged evaluator unexpectedly captured statement locals: {reprStr evaluated}")
  let lowered ← match SourceCoreElaboration.elaborateFunction function with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"reference staged lets did not lower: {reprStr error}")
  let expected := Core.Word.ofNatModulo 100
  assertTrue (decide (lowered.inputs.values = [] ∧
      lowered.resolved = .word expected ∧ lowered.core = .word expected))
    "staged integer lets or local references survived Core lowering"
  let signature ← signatureNamed program "basic"
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] 1 with
  | .ok (.complete plan) =>
      assertTrue (plan.specializations.length == 1 && plan.callEdges.isEmpty)
        "staged local intrinsics created source-call edges"
  | result => throw (IO.userError
      s!"staged-local worklist did not close in one slot: {reprStr result}")

private def testShadowingIdentity : IO Unit := do
  let program ← checkedProgram positiveSource
  let function ← checkedNamed program "shadow"
  let roots ← statementRoots function
  let (firstStatement, secondStatement, returnStatement) ← match roots with
    | [first, second, result] => pure (first, second, result)
    | _ => throw (IO.userError "shadow fixture lost its three statements")
  let (first, _) ← letBinding function firstStatement
  let (second, secondInitializer) ← letBinding function secondStatement
  let secondArguments ← builtinArguments function secondInitializer .integerAdd
  let priorReference ← match secondArguments with
    | reference :: _ => pure reference
    | _ => throw (IO.userError "shadowing initializer lost prior reference")
  localReference function priorReference first
  let returned ← returnedExpression function returnStatement
  let outer ← builtinArguments function returned .wordFromInteger
  let finalReference ← match outer with
    | [reference] => pure reference
    | _ => throw (IO.userError "shadowing return lost final reference")
  localReference function finalReference second
  assertTrue (first.name == second.name && first.id != second.id)
    "shadowed staged binders did not retain distinct lexical identities"

private def assertPreparedWord (moduleId : Workspace.ModuleId)
    (name : String) (expected : Core.Word) : IO Unit := do
  let prepared ← match prepare (workspace positiveSource)
      (Seed.named moduleId name) limits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"{name}: staged-local public preparation failed: {reprStr error}")
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .word expected ∧
      prepared.entry.elaborated.core = .word expected))
    s!"{name}: staged lets were not erased to one Word constant"
  let store : Core.Store := [.bool true, .word (Core.Word.ofNatModulo 37)]
  assertTrue (decide (prepared.run? [] limits.executionFuel store =
      some (.done (.word expected) store)))
    s!"{name}: staged-local execution changed result or store"

private def assertPreparedRoundtripEq (moduleId : Workspace.ModuleId) : IO Unit := do
  let prepared ← match prepare (workspace positiveSource)
      (Seed.named moduleId "roundtripEq") limits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"roundtripEq: public preparation failed: {reprStr error}")
  let one := Core.Word.ofNatModulo 1
  let zero := Core.Word.ofNatModulo 0
  let expectedResolved : Resolved.Expr :=
    .ifE (.bool true) (.word one) (.word zero)
  let expectedCore : Core.Expr :=
    .ifE (.bool true) (.word one) (.word zero)
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = expectedResolved ∧
      prepared.entry.elaborated.core = expectedCore))
    "roundtripEq: local cross-domain equality did not become a closed Bool guard"
  let store : Core.Store := [.word (Core.Word.ofNatModulo 41)]
  assertTrue (decide (prepared.run? [] limits.executionFuel store =
      some (.done (.word one) store)))
    "roundtripEq: staged equality selected the wrong Word branch or changed store"

private def testPublicExecution : IO Unit := do
  let moduleId ← mainModule
  let cases : List (String × Core.Word) := [
    ("basic", Core.Word.ofNatModulo 100),
    ("negative", Core.Word.ofIntModulo (-15)),
    ("reuse", Core.Word.ofIntModulo (-2)),
    ("shadow", Core.Word.ofNatModulo 4),
    ("chain", Core.Word.ofNatModulo 5),
    ("unused", Core.Word.ofNatModulo 7),
    ("composed", Core.Word.ofNatModulo 12)
  ]
  for (name, expected) in cases do
    assertPreparedWord moduleId name expected
  assertPreparedRoundtripEq moduleId
  let program ← checkedProgram positiveSource
  let unused ← checkedNamed program "unused"
  assertTrue (unused.solvedRequirements.length == 3)
    "unused eager initializer or returned Word lost literal obligations"

private def testRuntimeLetBoundary : IO Unit := do
  let program ← checkedProgram positiveSource
  let function ← checkedNamed program "runtimeWord"
  let roots ← statementRoots function
  let binder ← match roots with
    | letStatement :: _ =>
        match function.typedBody.lookupStatement? letStatement with
        | some { form := .letDecl binder (some _), .. } => pure binder
        | node => throw (IO.userError
            s!"runtime Word fixture lost its let: {reprStr node}")
    | [] => throw (IO.userError "runtime Word fixture lost its statements")
  let lowered ← match SourceCoreElaboration.elaborateFunction function with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"ordinary Word let stopped lowering: {reprStr error}")
  match lowered.resolved, lowered.core with
  | .letE actual _ _, .letE _ _ =>
      assertTrue (actual == binder.id)
        "ordinary Word let changed its resolved binder identity"
  | resolved, core => throw (IO.userError
      s!"ordinary Word let was incorrectly staged away: {reprStr resolved}, {reprStr core}")
  let store : Core.Store := [.bool false]
  assertTrue (decide (Core.runStateful 64
      (.initial lowered.core [.word (Core.Word.ofNatModulo 3)] store) =
        .done (.word (Core.Word.ofNatModulo 8)) store))
    "ordinary Word let lost runtime semantics or store preservation"

private def expectSourceCoreError (label content name : String)
    (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId name) limits with
  | .error (.linking (.sourceCore error)) =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong source-Core error {reprStr error}"
  | result => throw (IO.userError
      s!"{label}: invalid staged local was not rejected: {reprStr result}")

private def testBoundaryRejections : IO Unit := do
  let parameterSource := String.intercalate "\n" [
    "function parameter(value: integer) returns (Word) {",
    "  let local: integer = value;",
    "  return wordFromInteger(local);",
    "}"
  ]
  let parameterProgram ← checkedProgram parameterSource
  let parameter ← checkedNamed parameterProgram "parameter"
  let input ← match parameter.typedBody.inputs with
    | [input] => pure input
    | inputs => throw (IO.userError
        s!"integer parameter fixture retained {inputs.length} inputs")
  expectSourceCoreError "integer parameter is not a staged local"
    parameterSource "parameter" (.binder input.id) fun reason =>
      reason == .unsupportedType Ty.integer

  let uninitializedSource := String.intercalate "\n" [
    "function uninitialized() returns (Word) {",
    "  let value: integer;",
    "  return wordFromInteger(value);",
    "}"
  ]
  let uninitializedProgram ← checkedProgram uninitializedSource
  let uninitialized ← checkedNamed uninitializedProgram "uninitialized"
  let roots ← statementRoots uninitialized
  let first ← match roots with
    | first :: _ => pure first
    | [] => throw (IO.userError "uninitialized fixture lost its let")
  expectSourceCoreError "uninitialized staged local" uninitializedSource
    "uninitialized" (.occurrence first.occurrence) fun reason =>
      reason == .uninitializedLet

  let strictSource := String.intercalate "\n" [
    "function strict(value: Word) returns (Word) {",
    "  let ignored: integer = wordToInteger(value);",
    "  return 7;",
    "}"
  ]
  let strictProgram ← checkedProgram strictSource
  let strict ← checkedNamed strictProgram "strict"
  let strictRoots ← statementRoots strict
  let strictLet ← match strictRoots with
    | first :: _ => pure first
    | [] => throw (IO.userError "strict fixture lost its let")
  let (_, strictInitializer) ← letBinding strict strictLet
  let wordArguments ← builtinArguments strict strictInitializer .wordToInteger
  let runtimeWord ← match wordArguments with
    | [argument] => pure argument
    | _ => throw (IO.userError "strict wordToInteger lost its argument")
  expectSourceCoreError "unused initializer remains strict" strictSource
    "strict" (.occurrence runtimeWord.occurrence) fun reason =>
      reason == .stagedWordExpressionNotClosed

/-- Exercise eager let-bound staged integers through checking, linking, and execution. -/
def testSourceStagedIntegerLocals : IO Unit := do
  testReferenceCarrier
  testShadowingIdentity
  testPublicExecution
  testRuntimeLetBoundary
  testBoundaryRejections
  IO.println "let-bound staged integer checks GREEN"

end Tests.SourceStagedIntegerLocals
