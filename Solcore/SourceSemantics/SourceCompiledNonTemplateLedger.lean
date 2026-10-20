import Solcore.SourceSemantics.SourceSpecializedNonTemplateLedger
import Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalSpecializationOrigins
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedFinalPlanOrigins

/-! The real public compilation and every final cached row supply the closed
non-template branch of the original finalizer ledger. Later helper and method
rows use their actual accepted preparation and specialization receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledNonTemplateLedger
open Frontend SourceInference TypeSystem
open SourceCompiledLocalFinalization
open SourceSpecializedNonTemplateLedger

def Closed (row : SourceSpecialization.SpecializedFunction) : Prop :=
  ∀ requirement ∈ row.function.solvedRequirements,
    requirement.id ∉ sourceLocalSchemeTemplateIds row.function.typedBody →
      TypedTraitResolution.predicateVariables requirement.predicate = []

theorem initial_closed {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.plan.specializations) : Closed row := by
  have checked := SourceCoreCompiler.compile_checked_source accepted
  have lowered : SourceCoreCompiler.compileChecked compiled.program seeds options = .ok compiled := by
    simpa only [SourceCoreCompiler.compile, checked, Except.mapError, bind, Except.bind] using accepted
  obtain ⟨requests, ran⟩ := SourceCompiledLocalReadOrigins.compileChecked_worklist lowered
  obtain ⟨original, _, signature, supplied, specialized⟩ :=
    SourceSpecializationWorklist.run_original ran member
  exact fun _ present ordinary => specialized_closed specialized present ordinary

/-- This includes rows added by implementation-method selection and their
ordinary descendants, without initial-worklist membership. -/
theorem cached_closed (cached : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named) :
    Closed named.specialized := by
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached
  have member := CoreLowering.RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  obtain ⟨signature, original, supplied, specialized⟩ :=
    CoreLowering.CallablePreparedFinalSpecializationOrigins.of_default_preparation prepared _ member
  exact fun _ present ordinary => specialized_closed specialized present ordinary

theorem finalized_closed {row : SourceSpecialization.SpecializedFunction}
    {original : CheckedFunction} {environment : ProgramEnvironment}
    {signatures : ProgramSignatures} {signature : ProgramFunctionSignature} {fuel : Nat}
    (body : BodyReceipt environment signatures signature fuel original)
    (same : row.function = SourceSpecialization.applyCheckedFunction row.parameterSubstitution original)
    (closed : Closed row)
    {requirement : SolvedRequirement}
    (member : requirement ∈ body.finalized.solvedRequirements)
    (ordinary : requirement.id ∉ sourceLocalSchemeTemplateIds body.finalized.typedSource) :
    TypedTraitResolution.predicateVariables requirement.predicate = [] := by
  apply original_closed_of_application closed same
  · simpa only [body.solved] using member
  · simpa only [body.source] using ordinary

theorem selected_closed {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel) (closed : Closed row)
    {requirement : SolvedRequirement}
    (member : requirement ∈ selected.body.finalized.solvedRequirements)
    (ordinary : requirement.id ∉ sourceLocalSchemeTemplateIds selected.body.finalized.typedSource) :
    TypedTraitResolution.predicateVariables requirement.predicate = [] :=
  finalized_closed selected.body selected.specialized closed member ordinary

theorem compile_selected_closed {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (rowMember : row ∈ compiled.plan.specializations) {fuel : Nat}
    (selected : Selected compiled row fuel)
    {requirement : SolvedRequirement}
    (member : requirement ∈ selected.body.finalized.solvedRequirements)
    (ordinary : requirement.id ∉ sourceLocalSchemeTemplateIds selected.body.finalized.typedSource) :
    TypedTraitResolution.predicateVariables requirement.predicate = [] :=
  selected_closed selected (initial_closed accepted rowMember) member ordinary

theorem cached_selected_closed {compiled : SourceCoreCompiler.Compiled}
    (cached : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    {row : SourceSpecialization.SpecializedFunction} (same : named.specialized = row)
    {fuel : Nat} (selected : Selected compiled row fuel)
    {requirement : SolvedRequirement}
    (member : requirement ∈ selected.body.finalized.solvedRequirements)
    (ordinary : requirement.id ∉ sourceLocalSchemeTemplateIds selected.body.finalized.typedSource) :
    TypedTraitResolution.predicateVariables requirement.predicate = [] := by
  apply selected_closed selected _ member ordinary
  simpa only [same] using cached_closed cached position

end Solcore.SourceSemantics.SourceCompiledNonTemplateLedger
