import Solcore.SourceSemantics.CoreLowering.CallableCoercionBodyProvenance
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual generic coercion rechecking is tied to the loaded method carrier,
then to structural source substitution. Executable checks use the public Core
boundary; they do not stand in for source coercion execution proofs. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableCoercionBodyProvenance
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableCoercionBodyProvenance

/-- No separate recheck equality or generic source-body premise is supplied. -/
theorem actual_method_body {loaded : LoadedProgram} {program : CheckedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {coercion : CoercionStep}
    {method : ExecutableImplMethods.CheckedMethod}
    (accepted : SourceCompilationPlan.checkedCoercionMethod program caller node available coercion = .ok method) :
    ∃ retained, retained ∈ program.methods ∧ retained.id = method.id ∧
      method.specialized.function.typedBody = StructuralSubstitution.applyTypedSource
        method.specialized.parameterSubstitution retained.checked.typedBody ∧
      method.specialized.function.solvedRequirements = retained.checked.solvedRequirements.map
        (StructuralSubstitution.applySolvedRequirement method.specialized.parameterSubstitution) := by
  obtain ⟨receipt⟩ := of_accepted loadedAccepted accepted
  exact ⟨receipt.retained, receipt.retainedMember, receipt.retainedId, receipt.body, receipt.ledger⟩

/-- Actual plan extension supplies emitted carrier identity, independently of
same-fuel loaded body checking. Neither a source call nor closure history is assumed. -/
theorem actual_emitted_body {loaded : LoadedProgram} {program : CheckedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
    {project : CallableCoercionSpine.Projector} {context : CallableCoercionSpine.Context}
    {caller : SourceSpecialization.SpecializedFunction} {available : CallableCoercionSpine.RuntimeEvidence}
    {scope : CallableCoercionSpine.Scope} {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : CallableCoercionSpine.Lowered} {coercion : CoercionStep} {call : CallableCoercionSpine.Call}
    (step : CallableCoercionSpine.Step program project context caller available scope node policy input coercion output call)
    {before : SourceSpecializationWorklist.Plan} {edge : SourceSpecializationWorklist.CallEdge} {budget : Nat}
    (extended : SourceSpecializationWorklist.extendCompletePlan program before step.method.specialized edge budget =
      .ok (.complete context.plan)) :
    ∃ retained, retained ∈ program.methods ∧ retained.id = step.method.id ∧
      step.specialized.function.typedBody = StructuralSubstitution.applyTypedSource
        step.specialized.parameterSubstitution retained.checked.typedBody ∧
      step.specialized.function.solvedRequirements = retained.checked.solvedRequirements.map
        (StructuralSubstitution.applySolvedRequirement step.specialized.parameterSubstitution) := by
  rw [CallableCoercionPlanProvenance.step_specialized step extended]
  exact actual_method_body loadedAccepted step.selectedMethod

/-- The retained body's context, owner and root order are tied to that same
carrier, rather than reconstructed from the specialized key. -/
theorem context_and_owner {program : CheckedProgram} {method : ExecutableImplMethods.CheckedMethod}
    (receipt : Certificate program method) :
    method.specialized.function.typedBody.owner = receipt.implementation.id ∧
    method.specialized.function.typedBody.inputs = receipt.retained.checked.typedBody.inputs.map
      (StructuralSubstitution.applyBinder method.specialized.parameterSubstitution) ∧
    method.specialized.function.typedBody.roots = receipt.retained.checked.typedBody.roots :=
  ⟨receipt.owner, receipt.inputs, receipt.roots⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Word> {}",
    "trait Witness<T> {}", "impl Witness<Word> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "function hold<T>(value: T) returns (T) where T: Witness { return value; }",
    "impl<T> Coerce<T, Bool> where T: Marker { function coerce(value: T) returns (Bool) where T: Witness { let local: T = hold(value); return true; } }",
    "function converted(value: Word) returns (Bool) where Word: Marker { return value; }"
  ]}] }

private def audit (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let program := entry.cached.indexed.base.sourceProgram
  let mut observed := false
  for named in entry.cached.indexed.base.functions do
    if named.signature.key == entry.key then
      let caller := named.specialized
      let available ← SourceCompilerFeatureSupport.get "caller resolver"
        (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions)
      for item in caller.function.typedBody.nodes do
        match item with
        | .expression node =>
          for step in node.coercions do
            let method ← SourceCompilerFeatureSupport.get "actual coercion selector"
              (SourceCompilationPlan.checkedCoercionMethod program caller node available step)
            let implementation ← match program.signatures.implementations.filter (·.id == method.id.implementation) with
              | [value] => pure value | _ => throw (IO.userError "implementation singleton missing")
            let declaration ← match implementation.methods.filter (·.id == method.id) with
              | [value] => pure value | _ => throw (IO.userError "method singleton missing")
            let trait ← match program.signatures.trait? declaration.traitMethod.trait with
              | some value => pure value | _ => throw (IO.userError "trait missing")
            let retained ← match program.methods.filter (·.id == method.id) with
              | [value] => pure value | _ => throw (IO.userError "retained generic method missing")
            let generic ← SourceCompilerFeatureSupport.get "same-fuel complete recheck"
              (checkFunctionBody program.environment program.signatures
                (implementation.functionSignatureOfMethodWithTrait trait declaration) 1024)
            SourceCompilerFeatureSupport.require (generic == retained.checked)
              "same-fuel full checker carrier changed"
            let substitution := method.specialized.parameterSubstitution
            SourceCompilerFeatureSupport.require (substitution.length == 1 && substitution.map Prod.snd == [.word])
              "generic method was not actually specialized"
            SourceCompilerFeatureSupport.require
              (method.checked == method.specialized.function && method.specialized.function == SourceSpecialization.applyCheckedFunction substitution retained.checked)
              "complete specialized carrier differs from retained application"
            SourceCompilerFeatureSupport.require
              (method.specialized.function.typedBody == StructuralSubstitution.applyTypedSource substitution retained.checked.typedBody &&
                !(method.specialized.function.typedBody == retained.checked.typedBody))
              "independent structural source substitution was trivial or changed"
            SourceCompilerFeatureSupport.require
              (!retained.checked.solvedRequirements.isEmpty &&
                method.specialized.function.solvedRequirements == retained.checked.solvedRequirements.map
                  (StructuralSubstitution.applySolvedRequirement substitution))
              "ordered generic evidence substitution changed"
            SourceCompilerFeatureSupport.require
              (method.specialized.assumptions == (implementation.methodAssumptions trait declaration).map (ProgramPredicate.applyParameters substitution) &&
                method.specialized.function.typedBody.owner == implementation.id &&
                method.specialized.function.typedBody.roots == retained.checked.typedBody.roots)
              "synthetic context/owner/roots changed"
            let emitted ← SourceCompilerFeatureSupport.get "plan selected method"
              (SourceCompilationPlan.exactSpecialization entry.cached.indexed.base.plan method.specialized.key)
            SourceCompilerFeatureSupport.require (emitted == method.specialized) "emitter selected another complete method carrier"
            observed := true
        | _ => pure ()
  SourceCompilerFeatureSupport.require observed "coercion not reached"

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "checker" (Frontend.checkProgram workspace 1024)
  let entry ← SourceCompilerFeatureSupport.compileNamed program "converted"
  audit entry
  entry.checkResume [SourceCompilerFeatureSupport.scalar 9] (.bool true) 7
  SourceCompilerFeatureSupport.require ((← entry.run [SourceCompilerFeatureSupport.scalar 0]) == .bool true)
    "specialized method execution changed"
  IO.println "coercion body provenance: same-fuel retained carrier, generic source/context/evidence substitution, plan identity and resume GREEN"

end Tests.SourceCoreCallableCoercionBodyProvenance
