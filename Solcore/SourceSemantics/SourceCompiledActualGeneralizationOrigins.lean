import Solcore.SourceSemantics.SourceInferenceActualGeneralizationInference
import Solcore.SourceSemantics.SourceInferenceActualGeneralizationCoverage
import Solcore.SourceSemantics.SourceCompiledActualCallScope
import Solcore.SourceSemantics.SourceBodyTemplateScope

/-! The original selected-body inference supplies every initialized binding's
exact execution path. This covers ordinary and method bodies with the same
checking receipt and preserves the original binder and initializer identities. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceCompiledGeneralizedSoundness
open SourceInferenceExecution

namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

/-- Empty initial source and ledgers provide the inventory's prerequisites.
No semantic source-typing or compilation-profile premise is required. -/
theorem actual_generalization_origins (selected : BodySelection compiled row fuel) :
    ActualGeneralization.Origins selected.inferenceCall (evidenceSource selected).nodes := by
  have ready : LocalGeneralizationEvents.Ready (initial selected.signature selected.body.declaration) := by
    refine ⟨State.initial_requirementsWellFormed _ _ _, ?_, ?_⟩
    · intro id impossible
      exact False.elim (List.not_mem_nil impossible)
    · intro node impossible
      exact False.elim (List.not_mem_nil impossible)
  have origins := ActualGeneralization.inferStatementsFuel_origins selected.body.inferred
    selected.inferenceCall_root ready ActualGeneralization.Origins.empty
  change ActualGeneralization.Origins selected.inferenceCall selected.body.returned.nodes
  rw [selected.body.returned_nodes]
  exact origins

/-- Each complete raw initialized binding comes from an actual statement or
header receipt reached by this same selected body's successful inference. -/
theorem actual_initialized_origin (selected : BodySelection compiled row fuel)
    {binding : InitializedLetBinding}
    (member : binding ∈ initializedLetBindings (evidenceSource selected)) :
    ∃ initializer, binding.initializer = .expression initializer ∧
      ActualGeneralization.Origin selected.inferenceCall binding.binder initializer :=
  selected.actual_generalization_origins.initialized member

/-- Every completed ordinary or method cache row has the same original
checking body and a complete inventory of actual generalization calls. -/
theorem cached_initialized_origins {raw : Workspace.RawWorkspace}
    {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named) :
    ∃ selected : BodySelection compiled named.specialized fuel,
      ∀ binding ∈ initializedLetBindings (evidenceSource selected),
        ∃ initializer, binding.initializer = .expression initializer ∧
          ActualGeneralization.Origin selected.inferenceCall binding.binder initializer := by
  have member := CoreLowering.RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  have origin := CoreLowering.CallablePreparedFinalCatalogOrigins.of_default_preparation
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached) _ member
  rw [(compiled.artifact_fields artifact).1] at origin
  obtain ⟨selected⟩ := SourceBodyTemplateScope.catalog_selection checked origin
  exact ⟨selected, fun _ member => selected.actual_initialized_origin member⟩

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
