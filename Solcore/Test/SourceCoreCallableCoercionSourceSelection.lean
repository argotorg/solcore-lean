import Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceSelection
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual method selection supplies the independent source judgment and exact
ordered dictionary. Runtime checks exercise the same accepted compiler paths;
source body invocation and installed closure history are separate obligations. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Tests.SourceCoreCallableCoercionSourceSelection
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering TypeSystem
open CallableNamedMetadata (environment)
open CallableCoercionMethodInstantiation (Formation bodyInstance)
open CallableCoercionSourceSelection

/-- Only source formation, caller alignment and the actual three compiler
receipts are inputs. No source-selection/dictionary/body-meaning law is assumed. -/
theorem accepted_source_selection {loaded : LoadedProgram} {program : CheckedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {available dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod} {context : SourceSemantics.Context}
    (accepted : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method)
    (formed : ∀ receipt : Certificate program caller node available step method,
      Formation receipt.selected.implementation receipt.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures program.signatures) method.specialized.parameterSubstitution)
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller method)
    (materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method = .ok dictionary) :
    Dynamic.OperatorMethodSelected (Program.ofChecked program) context (environment available) "Coerce" "coerce"
      (step.requirement :: step.methodRequirements) (bodyInstance program method) (environment dictionary) := by
  obtain ⟨receipt⟩ := of_accepted accepted
  exact receipt.selects loadedAccepted (formed receipt) range signatures ledger assumptions resolved covered materialized

/-- A reached authentic primary row is enough even when unrelated ledger rows
are not valid. The actual materializer is not replaced with an invented map. -/
theorem reached_requirement {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {id : RequirementId} {goal : ProgramPredicate} {raw : TypedTraitResolution.Evidence} {context : SourceSemantics.Context}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available id goal = .ok raw)
    (valid : EvidenceValid [] program.signatures.resolutionRules goal (CallableNamedMetadata.evidence raw)) :
    Dynamic.RequirementProducesEvidence context (environment available) id goal (CallableNamedMetadata.evidence raw) ∧
      SourceCompilationPlan.materializeCallEvidence caller node.id available [id] [goal] = .ok [raw] :=
  ⟨requirement_produces signatures ledger assumptions resolved accepted valid, requirement_materialized accepted⟩

/-- The collector may visit the reverse order of the declaration. Its actual
first-match lookup at either parameter still agrees, without list equality. -/
theorem reversed_collector (first second : TypeParameterId) (different : first ≠ second) :
    let supplied : TypeSystem.ParameterSubstitution := [(first, .word), (second, .bool)]
    ([second, first].map fun key => (key, (supplied.lookup? key).getD (.parameter key))) ≠ supplied ∧
    (TypeSystem.ParameterSubstitution.lookup?
      ([second, first].map fun key => (key, (supplied.lookup? key).getD (.parameter key))) first).getD (.parameter first) = .word ∧
    (TypeSystem.ParameterSubstitution.lookup?
      ([second, first].map fun key => (key, (supplied.lookup? key).getD (.parameter key))) second).getD (.parameter second) = .bool := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro same
    have keys := congrArg (List.map Prod.fst) same
    simp only [List.map_cons, List.map_nil] at keys
    exact different (List.cons.inj keys).1.symm
  · rw [CallableCoercionMethodInstantiation.collected_lookup _ _ (by simp)]
    simp [TypeSystem.ParameterSubstitution.lookup?]
  · rw [CallableCoercionMethodInstantiation.collected_lookup _ _ (by simp)]
    simp [TypeSystem.ParameterSubstitution.lookup?, different]

/-- Groundness is weaker than source type formation: a missing nominal entry
is concrete to specialization but has no well-formed source range. -/
theorem ground_is_not_range (owner : Resolved.DeclarationId) (parameter : TypeParameterId) :
    SourceSpecialization.firstNonConcrete (.constructor (.declaration owner)) = none ∧
      ¬ SourceSemantics.ParameterSubstitution.RangeWellFormed
        (SourceSemantics.Context.ofSignatures ⟨[], [], [], [], [], []⟩) [(parameter, .constructor (.declaration owner))] := by
  refine ⟨rfl, ?_⟩
  intro valid
  have scopeProof := (valid parameter (.constructor (.declaration owner)) (by simp)).typeWellScoped
  generalize typeEq : Ty.constructor (TypeConstructorId.declaration owner) = type at scopeProof
  cases scopeProof <;> simp_all [SourceSemantics.Context.ofSignatures]

private def reorderedWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl<B, A> Coerce<(A, B), Bool> { function coerce(value: (A, B)) returns (Bool) { let visited: Word = 7; return true; } }",
    "function converted(left: Word, right: Bool) returns (Bool) { let value: (Word, Bool) = (left, right); return value; }"
  ]}] }

private def coveredWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Bool> {}",
    "trait Witness<T> {}", "impl Witness<Bool> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "impl Coerce<Bool, Word> where Bool: Marker { function coerce(value: Bool) returns (Word) where Bool: Witness { return value ? 17 : 4; } }",
    "function covered(flag: Bool) returns (Word) where Bool: Marker, Bool: Marker { return flag; }",
    "function uncovered(flag: Bool) returns (Word) { return flag; }"
  ]}] }

private def audit (entry : SourceCompilerFeatureSupport.Entry) (reordered expectedCovered : Bool) : IO Unit := do
  let base := entry.cached.indexed.base
  let program := base.sourceProgram
  let mut observed := false
  for named in base.functions do
    if named.signature.key == entry.key then
      let caller := named.specialized
      let available ← SourceCompilerFeatureSupport.get "caller resolver32"
        (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions)
      for item in caller.function.typedBody.nodes do
        match item with
        | .expression node =>
          for step in node.coercions do
            let method ← SourceCompilerFeatureSupport.get "coercion selector"
              (SourceCompilationPlan.checkedCoercionMethod program caller node available step)
            let dictionary ← SourceCompilerFeatureSupport.get "method dictionary"
              (SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method)
            let implementation ← match program.signatures.implementations.filter (·.id == method.id.implementation) with
              | [value] => pure value | _ => throw (IO.userError "implementation singleton missing")
            let declaration ← match implementation.methods.filter (·.id == method.id) with
              | [value] => pure value | _ => throw (IO.userError "method singleton missing")
            let trait ← match program.signatures.trait? declaration.traitMethod.trait with
              | some value => pure value | _ => throw (IO.userError "trait missing")
            let retained ← match program.methods.filter (·.id == method.id) with
              | [value] => pure value | _ => throw (IO.userError "retained method missing")
            let primaryRow ← match caller.function.solvedRequirements.filter (·.id == step.requirement) with
              | [value] => pure value | _ => throw (IO.userError "primary singleton missing")
            let matched ← match TypedTraitResolution.matchImplHeadWithParameters? implementation.parameters
                implementation.implRule primaryRow.predicate with
              | some value => pure value | _ => throw (IO.userError "actual head match missing")
            let substitution := method.specialized.parameterSubstitution
            let collector := TypedTraitResolution.ruleParameters implementation.implRule
            SourceCompilerFeatureSupport.require
              (substitution.map Prod.fst == implementation.parameters &&
                ProgramPredicate.applyParameters substitution implementation.head == primaryRow.predicate)
              "source-order head instantiation changed"
            for parameter in implementation.parameters do
              SourceCompilerFeatureSupport.require (substitution.lookup? parameter == matched.parameterSubstitution.lookup? parameter)
                "collector and canonical lookup differ"
            if reordered then
              SourceCompilerFeatureSupport.require (collector == implementation.parameters.reverse && collector != implementation.parameters &&
                substitution.map Prod.snd == [.bool, .word]) "two-parameter order fixture became trivial"
            SourceCompilerFeatureSupport.require
              (method.methodPredicates == declaration.wherePredicates.map (ProgramPredicate.applyParameters substitution) &&
                method.specialized.assumptions == (implementation.methodAssumptions trait declaration).map (ProgramPredicate.applyParameters substitution) &&
                dictionary.map SourceCompilationPlan.runtimeEvidenceGoal == method.specialized.assumptions)
              "source requirements or ordered dictionary changed"
            let covered := method.traitPredicates.all caller.assumptions.contains
            SourceCompilerFeatureSupport.require (covered == expectedCovered) "caller coverage profile changed"
            let headers ← SourceCompilerFeatureSupport.get "header resolver32"
              (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program method.specialized.key method.traitPredicates)
            SourceCompilerFeatureSupport.require
              (dictionary == headers ++ method.implementationPremises ++ method.methodPremises)
              "actual dictionary lost an ordered component"
            if covered then
              for fresh in headers do
                let found := available.find? fun raw => SourceCompilationPlan.runtimeEvidenceGoal raw == SourceCompilationPlan.runtimeEvidenceGoal fresh
                SourceCompilerFeatureSupport.require (found == some fresh) "caller first match differs from fresh full evidence"
            if !reordered then
              SourceCompilerFeatureSupport.require (dictionary.length == 3 &&
                dictionary[0]? == dictionary[1]? && dictionary[1]? != dictionary[2]?) "duplicate/header/method order not exercised"
            let emitted ← SourceCompilerFeatureSupport.get "actual selected full carrier"
              (SourceCompilationPlan.exactSpecialization base.plan method.specialized.key)
            SourceCompilerFeatureSupport.require (emitted == method.specialized &&
              emitted.function.typedBody == StructuralSubstitution.applyTypedSource substitution retained.checked.typedBody &&
              emitted.function.solvedRequirements == retained.checked.solvedRequirements.map
                (StructuralSubstitution.applySolvedRequirement substitution) &&
              emitted.function.typedBody.owner == implementation.id)
              "selected source body/owner/ordered ledger changed"
            observed := true
        | _ => pure ()
  SourceCompilerFeatureSupport.require observed "actual coercion site was not reached"

def run : IO Unit := do
  let reordered ← SourceCompilerFeatureSupport.get "two-parameter checker" (checkProgram reorderedWorkspace 1024)
  let entry ← SourceCompilerFeatureSupport.compileNamed reordered "converted"
  audit entry true true
  entry.checkResume [SourceCompilerFeatureSupport.scalar 8, .bool false] (.bool true) 7
  let covered ← SourceCompilerFeatureSupport.get "dictionary checker" (checkProgram coveredWorkspace 1024)
  for name in ["covered", "uncovered"] do
    let entry ← SourceCompilerFeatureSupport.compileNamed covered name
    audit entry false (name == "covered")
    entry.checkResume [.bool true] (SourceCompilerFeatureSupport.scalar 17) 7
    SourceCompilerFeatureSupport.require ((← entry.run [.bool false]) == SourceCompilerFeatureSupport.scalar 4)
      "source selection fixture false result changed"
  IO.println "coercion source selection: collector/declaration order, retained body, full dictionaries, duplicate goals and covered/uncovered profiles GREEN"

end Tests.SourceCoreCallableCoercionSourceSelection
