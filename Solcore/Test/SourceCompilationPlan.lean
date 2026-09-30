import Solcore.Frontend.SourceCompilationPlan
import Solcore.Frontend.SourceCompilationPlan.Canonical

/-! Compilation preparation must work without importing either evaluator. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.Value
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreDirectLinking.link

set_option autoImplicit false

namespace Tests.SourceCompilationPlan

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{
    path := "main.solc"
    content := String.intercalate "\n" [
      "trait Coerce<From, To> {",
      "  function coerce(value: From) returns (To);",
      "}",
      "function helper(value: Word) returns (Word) { return value; }",
      "impl Coerce<Bool, Word> {",
      "  function coerce(value: Bool) returns (Word) {",
      "    let selected: function(Word) returns(Word) = helper;",
      "    return selected(value ? 41 : 7);",
      "  }",
      "}",
      "function entry(value: Bool) returns (Word) { return value; }"
    ]
  }]
  externalLibraries := []
}

private def preparedInput : IO (CheckedProgram × SourceSpecializationWorklist.Plan) := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"plan fixture: {reprStr errors}")
  let entry ← match program.signatures.functions.filter (·.name == "entry") with
    | [entry] => pure entry
    | _ => throw (IO.userError "plan fixture: missing entry")
  let request : SourceSpecializationWorklist.Request := {
    declaration := entry.id
    parameterSubstitution := []
  }
  let plan ← match SourceSpecializationWorklist.run program [request] 8 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"plan fixture worklist: {reprStr result}")
  pure (program, plan)

/-- Selected coercions can introduce a first-class helper absent from the
ordinary source-call frontier. Preparation must retain it before execution. -/
private def testSelectedMethodFrontier (program : CheckedProgram)
    (plan : SourceSpecializationWorklist.Plan) : IO Unit := do
  assertTrue (plan.specializations.length == 1 && plan.referenceEdges.isEmpty)
    "ordinary worklist unexpectedly included the detached coercion method"
  let prepared ← match SourceCompilationPlan.prepareExecutablePlanEvidence program plan with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"prepare plan: {reprStr error}")
  let helper ← match program.signatures.functions.filter (·.name == "helper") with
    | [helper] => pure helper
    | _ => throw (IO.userError "plan fixture: missing helper")
  assertTrue (prepared.specializations.length == 3)
    "preparation lost a selected method or its helper"
  assertTrue (prepared.referenceEdges.any fun edge =>
      decide (edge.callee.declaration = helper.id))
    "preparation lost the first-class helper reference"
  assertTrue (prepared.seedKeys == plan.seedKeys)
    "preparation changed the public roots"
  match SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program plan 1 8 with
  | .error (.executablePlanClosureFuelExhausted 1) => pure ()
  | result => throw (IO.userError s!"closure budget was not enforced: {reprStr result}")
  match SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program plan 8 0 with
  | .error (.coercionMethodSpecializationBudgetExhausted ..) => pure ()
  | result => throw (IO.userError s!"helper budget was not enforced: {reprStr result}")

private def testCanonicalRejections (program : CheckedProgram)
    (plan : SourceSpecializationWorklist.Plan) : IO Unit := do
  match SourceCompilationPlan.Canonical.validatePlan program plan with
  | .ok () => pure ()
  | .error error => throw (IO.userError s!"canonical plan rejected: {reprStr error}")
  let forged := { plan with seedKeys := [] }
  match SourceCompilationPlan.validateCanonicalInputPlan program forged with
  | .error .nonCanonicalInputPlan => pure ()
  | result => throw (IO.userError s!"orphaned frontier accepted: {reprStr result}")
  let duplicate := { plan with specializations := plan.specializations ++ plan.specializations }
  match SourceCompilationPlan.Canonical.validatePlan program duplicate with
  | .error (.duplicateSpecialization _) => pure ()
  | result => throw (IO.userError s!"duplicate plan diagnosis changed: {reprStr result}")

def testSourceCompilationPlan : IO Unit := do
  let (program, plan) ← preparedInput
  testSelectedMethodFrontier program plan
  testCanonicalRejections program plan

end Tests.SourceCompilationPlan
