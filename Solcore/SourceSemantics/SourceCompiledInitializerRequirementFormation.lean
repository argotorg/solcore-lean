import Solcore.SourceSemantics.SourceCompiledTopLevelInitializerContinuation
import Solcore.SourceSemantics.SourceInferenceRetainedRequirementFormation

/-! The selected initializer's actual continuation and finalizer discharge the
normalization assumptions of retained requirement formation. Only the genuine
issuance formation remains to be supplied by the recursive source traversal. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness

variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : Selected compiled row fuel} {source : Syntax.Statement}

theorem retained_formation (continuation : InitializerContinuation selected source)
    {target : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed (localSchemeInitializerContext target
      (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)))
    (signatures : target.signatures = compiled.program.signatures)
    (parameters : target.typeParameters = selected.signature.scheme.parameters)
    (owner : target.currentDeclaration = some selected.body.declaration.id)
    (residual : target.residualTypeVariables = true)
    (issued : ∀ requirement ∈ continuation.receipt.ready.requirements,
      requirement.id ∈ localSchemeTemplateIds continuation.receipt.binding.1 →
        PredicateAdmissible (localSchemeInitializerContext target
          (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution))
          requirement.predicate) :
    RetainedRequirementPredicateFormationAt continuation.receipt.ready
      continuation.receipt.binding.1 selected.body.finalized.substitution target := by
  exact SourceInferenceRequirementFormation.retained_formation_of_issuances
    selected.body.resources binders signatures parameters owner residual
    continuation.substitution continuation.no_capture issued

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerContinuation
