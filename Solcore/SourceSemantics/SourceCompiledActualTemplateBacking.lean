import Solcore.SourceSemantics.SourceCompiledActualBodyInputs
import Solcore.SourceSemantics.SourceInferenceActualTemplateBacking
import Solcore.SourceSemantics.SourceBodyTemplateScope

/-! The actual initialized body, including a cached method body, supplies
raw local-template witnesses throughout its reached inference calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceInferenceExecution ProtectedVariables
namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem inferenceCall_liveTemplatesBacked (selected : BodySelection compiled row fuel) :
    LiveTemplatesBacked selected.inferenceCall.initial :=
  LiveTemplatesBacked.initial _ _ _

theorem actualCall_liveTemplatesBacked (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    LiveTemplatesBacked call.initial :=
  here.liveTemplatesBacked (selected.inferenceCall_inputs checked)
    selected.inferenceCall_liveTemplatesBacked

/-- Each prepared ordinary or method cache row supplies these same witnesses
at all calls in its original successful inference. -/
theorem cached_liveTemplatesBacked
    {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named) :
    ∃ selected : BodySelection compiled named.specialized fuel,
      ∀ call, selected.InferenceCall call → LiveTemplatesBacked call.initial := by
  have member := CoreLowering.RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  have origin := CoreLowering.CallablePreparedFinalCatalogOrigins.of_default_preparation
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached) _ member
  rw [(compiled.artifact_fields artifact).1] at origin
  obtain ⟨selected⟩ := SourceBodyTemplateScope.catalog_selection checked origin
  exact ⟨selected, fun _ here => selected.actualCall_liveTemplatesBacked checked here⟩

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
