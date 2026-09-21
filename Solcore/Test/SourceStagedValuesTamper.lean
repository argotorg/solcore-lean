import Solcore

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

/-- Fix the defensive ADR-0358 rejection and validation-order boundaries. -/
def testSourceStagedValuesTamper : IO Unit := do
  let program ← checkedProgram
  testForgedAnalysisRejected program
  testForgedKeyRejected program
  testTotalArityReported program
  testGuardTypePrecedesBranchStage program

end Tests.SourceStagedValuesTamper
