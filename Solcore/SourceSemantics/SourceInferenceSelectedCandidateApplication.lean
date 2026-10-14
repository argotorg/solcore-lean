import Solcore.SourceSemantics.SourceInferenceSelectedCandidateFitting

/-! The selected declaration keeps its full canonical substitution while
parameter and result formation are proved directly in the active context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem declarationApplication_afterSubstitution
    {context : SourceSemantics.Context} {substitution : Substitution}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible context substitution)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ context.signatures.functions) (next : Nat) :
    let instantiated := signature.scheme.instantiate next
    DeclarationApplicationValid context
      ((Frontend.SourceInference.DeclarationInstantiation.ofInstantiated signature instantiated).applySubstitution substitution)
      ((signature.parameterTypes.map instantiated.parameterSubstitution.apply).map substitution.apply)
      (substitution.apply (instantiated.parameterSubstitution.apply (Ty.productMany signature.returnTypes)))
      (instantiated.predicates.map (TypedTraitResolution.applySubstitution substitution)) := by
  let instantiated := signature.scheme.instantiate next
  have valid := declarationInstantiation_afterSubstitution catalog binders residual range member next
  have formed := catalog.functions_semantic signature member
  have exactDomain := DeclarationInstantiation.instantiate_parameterSubstitution_exact
    signature.scheme next (catalog.function_parameters signature member).1
  have parameters := FlexibleSubstitution.TypesWellScoped.applyFlexible_composeParameters
    (context := signatureContext context.signatures signature.id signature.scheme.parameters signature.scheme.predicates)
    substitution instantiated.parameterSubstitution exactDomain
    (StructuralSubstitution.TypesWellFormed.toTypesWellScoped formed.parameter_types)
  have returns := FlexibleSubstitution.TypeWellScoped.applyFlexible_composeParameters
    (context := signatureContext context.signatures signature.id signature.scheme.parameters signature.scheme.predicates)
    substitution instantiated.parameterSubstitution exactDomain
    (StructuralSubstitution.TypesWellScoped.productMany
      (StructuralSubstitution.TypesWellFormed.toTypesWellScoped formed.return_types))
  refine .intro member valid rfl ?_ ?_ ?_ rfl
  · exact parameters.symm
  · exact returns.symm
  · change substitution.apply instantiated.body = _
    rw [ConstrainedDeclarationScheme.instantiate_body, formed.scheme_body,
      StructuralSubstitution.apply_function, StructuralSubstitution.apply_productMany,
      FlexibleSubstitution.apply_function, FlexibleSubstitution.apply_productMany]

theorem tryFunctionCandidate_application_afterSubstitution
    {inferenceContext : Frontend.SourceInference.Context}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {attempt : Detail.CandidateAttemptResult}
    {active : SourceSemantics.Context} {substitution : Substitution}
    (catalog : SignatureCatalogWellFormed active.signatures)
    (binders : TypeParameterBindersWellFormed active)
    (residual : active.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible active substitution)
    (member : signature ∈ active.signatures.functions)
    (success : Detail.tryFunctionCandidate inferenceContext arguments integerLiteralOrigins
      call expected state signature = .ok (some attempt)) :
    let instantiated := signature.scheme.instantiate state.inference.next
    DeclarationApplicationValid active (attempt.instantiation.applySubstitution substitution)
      ((signature.parameterTypes.map instantiated.parameterSubstitution.apply).map substitution.apply)
      (substitution.apply (instantiated.parameterSubstitution.apply (Ty.productMany signature.returnTypes)))
      (instantiated.predicates.map (TypedTraitResolution.applySubstitution substitution)) := by
  rw [Detail.tryFunctionCandidate_some_instantiation success]
  exact declarationApplication_afterSubstitution catalog binders residual range member state.inference.next

end Solcore.SourceSemantics.SourceInferenceSoundness
