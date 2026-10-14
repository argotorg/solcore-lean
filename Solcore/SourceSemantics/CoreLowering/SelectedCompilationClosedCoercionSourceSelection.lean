import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedCoercionSelection

/-! Actual method selection and dictionary materialization determine the
original Source coercion rule before either body executes. Closed catalog
facts discharge formation, full substitution range and caller coverage. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationClosedCoercionSourceSelection
open Core Frontend SourceInference
open CallableCoercionMethodInstantiation (Formation bodyInstance)
open CallableNamedMetadata (environment)

theorem selects {compiled : SourceCoreUnifiedCompilation.Compiled}
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {available dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod}
    {context : SourceSemantics.Context}
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (catalog : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)
    (accepted : SourceCompilationPlan.checkedCoercionMethod compiled.sourceProgram caller node available step = .ok method)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment
      compiled.sourceProgram caller.key caller.assumptions = .ok available)
    (materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence
      compiled.sourceProgram caller node step method = .ok dictionary)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions) :
    Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context
      (environment available) "Coerce" "coerce" (step.requirement :: step.methodRequirements)
      (bodyInstance compiled.sourceProgram method) (environment dictionary) := by
  obtain ⟨receipt⟩ := CallableCoercionSourceSelection.of_accepted accepted
  let chosen := receipt.selected
  have formed : Formation chosen.implementation chosen.declaration :=
    catalog.formed chosen.implementation chosen.implementationMember chosen.declaration chosen.methodMember
  have parameters := catalog.parameters chosen.implementation chosen.implementationMember
    chosen.declaration chosen.methodMember
  have substitution : method.specialized.parameterSubstitution = [] :=
    List.map_eq_nil_iff.mp (chosen.domain.trans parameters)
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures)
      method.specialized.parameterSubstitution := by
    intro parameter replacement member
    rw [substitution] at member
    cases member
  have methodAssumptions : method.specialized.assumptions = [] := by
    rw [(CallableCoercionBodyProvenance.specialization_fields chosen.specialized).2]
    change List.map _ (chosen.implementation.methodAssumptions chosen.trait chosen.declaration) = []
    rw [catalog.assumptions chosen.implementation chosen.implementationMember
      chosen.declaration chosen.methodMember chosen.trait chosen.traitMember]
    rfl
  have covered : CallableCoercionEvidenceOrigins.CallerCovered caller method := by
    obtain ⟨headers, origins, assembled, goals⟩ := CallableCoercionEvidenceOrigins.materialized materialized
    have dictionaryEmpty : dictionary = [] := List.map_eq_nil_iff.mp (goals.trans methodAssumptions)
    have allEmpty := assembled.symm.trans dictionaryEmpty
    have headersEmpty : headers = [] :=
      (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp allEmpty).1).1
    rw [headersEmpty] at origins
    have traitPredicatesEmpty : method.traitPredicates = [] := by
      have lengths := origins.length_eq
      simpa using lengths
    intro goal member
    rw [traitPredicatesEmpty] at member
    cases member
  exact receipt.selects checked formed range signatures ledger assumptions resolved covered materialized

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationClosedCoercionSourceSelection
