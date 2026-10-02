import Solcore.SourceSemantics.CoreLowering.CallableCoercionPlanProvenance
import Solcore.Test.SourceCompilerFeatureSupport

/-! Complete carrier identity survives insertion, duplicate acceptance and a
later helper extension. Same keys with changed source, evidence or stage data
are rejected by the actual extension action. Source body semantics are separate. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableCoercionPlanProvenance
open Solcore Frontend SourceInference SourceSemantics.CoreLowering SourceSpecializationWorklist
open CallableCoercionPlanProvenance

/-- Two actual public extensions retain the original complete method carrier,
even when the later action supplies a different detached root. -/
theorem later_extension {program : CheckedProgram} {before middle final : Plan}
    {method helper : SourceSpecialization.SpecializedFunction} {edge other : CallEdge} {budget nextBudget : Nat}
    (first : extendCompletePlan program before method edge budget = .ok (.complete middle))
    (second : extendCompletePlan program middle helper other nextBudget = .ok (.complete final)) :
    SourceCompilationPlan.exactSpecialization final method.key = .ok method :=
  selected_after second (complete_root first)

/-- The proof records equality of the raw checked body and ordered ledger, not
only of the method key or the native signature. -/
theorem emitted_source_and_ledger {program : CheckedProgram} {project : CallableCoercionSpine.Projector}
    {context : CallableCoercionSpine.Context} {caller : SourceSpecialization.SpecializedFunction}
    {available : CallableCoercionSpine.RuntimeEvidence} {scope : CallableCoercionSpine.Scope}
    {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : CallableCoercionSpine.Lowered} {coercion : CoercionStep} {call : CallableCoercionSpine.Call}
    (step : CallableCoercionSpine.Step program project context caller available scope node policy input coercion output call)
    {before : Plan} {edge : CallEdge} {budget : Nat}
    (extended : extendCompletePlan program before step.method.specialized edge budget = .ok (.complete context.plan)) :
    step.specialized.function.typedBody = step.method.specialized.function.typedBody ∧
    step.specialized.function.solvedRequirements = step.method.specialized.function.solvedRequirements ∧
    step.specialized.assumptions = step.method.specialized.assumptions ∧
    step.specialized.stageAnalysis = step.method.specialized.stageAnalysis := by
  rw [step_specialized step extended]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Same-key carriers cannot pass comparison after any full-body change. -/
theorem changed_body_rejected {left right : SourceSpecialization.SpecializedFunction}
    (different : left.function.typedBody ≠ right.function.typedBody) : (left == right) = false := by
  cases same : (left == right) with
  | false => rfl
  | true => exact False.elim (different (congrArg (fun value => value.function.typedBody)
      (CallableSpecializationEquality.eq_of_beq same)))

theorem changed_stage_rejected {left right : SourceSpecialization.SpecializedFunction}
    (different : left.stageAnalysis ≠ right.stageAnalysis) : (left == right) = false := by
  cases same : (left == right) with
  | false => rfl
  | true => exact False.elim (different (congrArg (·.stageAnalysis)
      (CallableSpecializationEquality.eq_of_beq same)))

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Bool> {}",
    "trait Witness<T> {}", "impl Witness<Bool> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "function choose(flag: Bool) returns (Word) { return flag ? 17 : 4; }",
    "impl Coerce<Bool, Word> where Bool: Marker { function coerce(value: Bool) returns (Word) where Bool: Witness { let seen: Word = 2; let other: Word = 3; return choose(value); } }",
    "function converted(flag: Bool) returns (Word) where Bool: Marker { return flag; }"
  ]}] }

private def checkSelected (plan : Plan) (value : SourceSpecialization.SpecializedFunction) : IO Unit := do
  let actual ← SourceCompilerFeatureSupport.get "exact carrier" (SourceCompilationPlan.exactSpecialization plan value.key)
  SourceCompilerFeatureSupport.require (actual == value) "complete selected carrier changed"

private def audit (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let base := entry.cached.indexed.base
  let mut observed := false
  for named in base.functions do
    if named.signature.key == entry.key then
      let caller := named.specialized
      let available ← SourceCompilerFeatureSupport.get "caller" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
      for item in caller.function.typedBody.nodes do
        match item with
        | .expression node =>
          for step in node.coercions do
            let method ← SourceCompilerFeatureSupport.get "actual selected method"
              (SourceCompilationPlan.checkedCoercionMethod base.sourceProgram caller node available step)
            let root := method.specialized
            let edge : CallEdge := ⟨caller.key, node.id, root.key⟩
            let empty : Plan := ⟨[], [], [], []⟩
            let exhausted ← SourceCompilerFeatureSupport.get "zero helper budget"
              (extendCompletePlan base.sourceProgram empty root edge 0)
            match exhausted with
            | .budgetExhausted kept _ pending =>
                checkSelected kept root
                SourceCompilerFeatureSupport.require (!pending.isEmpty) "helper request was dropped"
            | .complete _ => throw (IO.userError "fixture did not reach the helper frontier")
            let outcome ← SourceCompilerFeatureSupport.get "insert detached method"
              (extendCompletePlan base.sourceProgram empty root edge 8)
            let inserted ← match outcome with
              | .complete plan => pure plan
              | _ => throw (IO.userError "helper closure exhausted")
            checkSelected inserted root
            SourceCompilerFeatureSupport.require (inserted.specializations.length == 2) "actual ordinary helper was not retained"
            let repeated ← SourceCompilerFeatureSupport.get "accept identical root"
              (extendCompletePlan base.sourceProgram inserted root edge 8)
            for old in inserted.specializations do checkSelected repeated.plan old
            SourceCompilerFeatureSupport.require (repeated.plan.specializations == inserted.specializations)
              "repeated root replaced or duplicated a carrier"
            let changedSource := {root with function := {root.function with typedBody :=
              {root.function.typedBody with owner := {root.function.typedBody.owner with declarationIndex := root.function.typedBody.owner.declarationIndex + 1}}}}
            let changedEvidence := {root with function := {root.function with solvedRequirements := root.function.solvedRequirements.reverse}}
            let changedAssumptions := {root with assumptions := root.assumptions.reverse}
            let changedStages := {root with stageAnalysis := {root.stageAnalysis with expressions := root.stageAnalysis.expressions.reverse}}
            for changed in [changedSource, changedEvidence, changedAssumptions, changedStages] do
              SourceCompilerFeatureSupport.require (changed.key == root.key && !(changed == root)) "mutation fixture did not change a non-key field"
              match extendCompletePlan base.sourceProgram inserted changed edge 8 with
              | .error (.existingSpecializationMismatch key) =>
                  SourceCompilerFeatureSupport.require (key == root.key) "wrong mismatched key"
              | _ => throw (IO.userError "same-key changed carrier was accepted")
            match extendCompletePlan base.sourceProgram {empty with specializations := [root, root]} root edge 8 with
            | .error (.duplicatePlanSpecializations key 2) =>
                SourceCompilerFeatureSupport.require (key == root.key) "wrong duplicate key"
            | _ => throw (IO.userError "duplicate root plan accepted")
            observed := true
        | _ => pure ()
  SourceCompilerFeatureSupport.require observed "coercion method not found"

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "checker" (checkProgram workspace)
  let entry ← SourceCompilerFeatureSupport.compileNamed program "converted"
  audit entry
  entry.checkResume [.bool true] (SourceCompilerFeatureSupport.scalar 17) 9
  SourceCompilerFeatureSupport.require ((← entry.run [.bool false]) == SourceCompilerFeatureSupport.scalar 4) "false result changed"
  IO.println "coercion plan: insertion, duplicate carrier, helper closure, full metadata rejection and resume GREEN"

end Tests.SourceCoreCallableCoercionPlanProvenance
