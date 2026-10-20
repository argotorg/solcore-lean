import Solcore.SourceSemantics.SourceInferenceNormalizedRequirementFormation
import Solcore.SourceSemantics.SourceCompiledInitializerRequirementFormation

/-! Selected actual continuation discharges normalization for prior local reads. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness

/-- The same selected initializer receipt and finalizer provide continuation
and no-capture for normalized issuances from earlier generalized binders. -/
theorem retained_normalized_formation
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : BodySelection compiled row fuel} {source : Syntax.Statement}
    (continuation : InitializerContinuation selected source)
    {target : SourceSemantics.Context}
    (issued : ∀ requirement ∈ continuation.receipt.ready.requirements,
      requirement.id ∈ localSchemeTemplateIds continuation.receipt.binding.1 →
      PredicateAdmissible (localSchemeInitializerContext target
        (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution))
        (TypedTraitResolution.applySubstitution selected.body.finalized.substitution requirement.predicate)) :
    RetainedRequirementPredicateFormationAt continuation.receipt.ready
      continuation.receipt.binding.1 selected.body.finalized.substitution target := by
  exact SourceInferenceRequirementFormation.retained_formation_of_normalized_issuances
    continuation.substitution continuation.no_capture issued

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerContinuation
