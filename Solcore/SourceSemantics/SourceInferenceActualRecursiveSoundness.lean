import Solcore.SourceSemantics.SourceInferenceActualRecursiveContracts

/-! Exact source-prefix expression typing is recovered from the corrected
retained contract, and whole-body inference retains actual context provenance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualInferExprFuelScopedSoundness_of_retainedSoundness
    {fuel : Nat}
    (retainedSound : ActualInferExprFuelRetainedSoundness fuel) :
    ActualInferExprFuelScopedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expression expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    resultExtension semanticExtension rawExtension integerPatternsSubset
    integerLiteralsSubset requirementsSubset covered actualCovered
  have resultToFinal : TypingSourceExtends
      ((resultState.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource :=
    TypingSourceExtends.trans resultExtension semanticExtension
  have requirementsRetained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id :=
    ExpressionRequirementsRetainedAt.ofTypingSourceExtends
      finalized.substitution resultToFinal
  have childrenRetained : ExpressionDirectChildrenRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id :=
    ExpressionDirectChildrenRetainedAt.ofTypingSourceExtends
      finalized.substitution resultToFinal
  have base := retainedSound success resources interfaces resultSubstitutionExtension
    signaturesEq ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    (ProperDescendantsPreserved.ofTypingSourceExtends resultToFinal)
    (RawProperDescendantsPreserved.ofTypingSourceExtends rawExtension)
    integerPatternsSubset integerLiteralsSubset requirementsSubset
    requirementsRetained
    (ExpressionCoercionPrimariesRetainedAt.ofTypingSourceExtends finalized.substitution resultToFinal)
    (ExpressionOperatorSiteRetainedAt.ofTypingSourceExtends finalized.substitution resultToFinal)
    childrenRetained covered
    (ProperDescendantsPreserved.ofTypingSourceExtends resultExtension) actualCovered
  cases base with
  | @intro node rawType plan contains typeEq formType rawAdmissible
      requirements =>
      have evidenceMember : Node.expression node ∈
          (evidenceState.toTypedSource roots).nodes :=
        rawExtension.nodes_prefix.subset contains.1
      have finalAdmissible : TypeAdmissible semanticContext
          (finalized.substitution.apply inferred.type) := by
        have nodeAdmissible := resources.expressionTypeAdmissible_in_active
          evidenceMember
          (invariant.typeParameterBinders (by
            simpa [ownerEq, typeParametersEq] using canonical))
          invariant.signatures_eq_whole invariant.typeParametersEq
          invariant.declarationEq invariant.residual
        simpa only [typeEq] using nodeAdmissible
      exact
        (ExpressionTypingBase.intro contains typeEq formType rawAdmissible
          requirements).expressionHasType
          (ExpressionNodesPreservedAt.ofTypingSourceExtends resultExtension)
          finalAdmissible


theorem actualInferStatementsFuelSoundness_of_scopedSoundness
    {fuel : Nat}
    (scopedSound : ActualInferStatementsFuelScopedSoundness fuel) :
    ActualInferStatementsFuelSoundness fuel := by
  intro inferenceContext statements expectedReturn initial result
    evidenceState roots finalized frames semanticContext success resources interfaces
    signatureFormation functionsCanonical catalog signatureParameters
    initialActive actual operational returnAdmissible initialSchemeIsolation ready returnBelow bindersBelow
    initialBelow
    finalSubstitutionExtension rawResultExtension resultExtension
    integerPatternsSubset integerLiteralsSubset requirementsSubset
    signaturesEq typeParametersEq declarationEq residual
    solvedRequirementsEq assumptionsMono covered actualCovered
  have progress := Detail.inferStatementsFuel_inferenceProperties ready
    signatureFormation functionsCanonical returnBelow success
  have initialSubstitutionExtension : finalized.substitution.SemanticallyExtends
      initial.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      finalSubstitutionExtension progress.1.substitution_extends
  have initialInvariant : RecursiveStatementInvariant inferenceContext
      expectedReturn finalized initial semanticContext := {
    active := initialActive
    ready
    returnBelow
    bindersBelow
    nodesBelow := initialBelow
    schemeIsolation := initialSchemeIsolation
    substitutionExtension := initialSubstitutionExtension
    signaturesEq
    typeParametersEq
    declarationEq
    residual
    solvedRequirementsEq
    assumptionsMono
  }
  obtain ⟨finalContext, facts, finalInvariant, finalActual, finalOperational, typing, agreement⟩ :=
    scopedSound (wholeContext := inferenceContext)
      (wholeReturn := expectedReturn)
      (semanticSource := finalized.typedSource)
      success resources interfaces rfl rfl rfl rfl signatureFormation
      functionsCanonical catalog signatureParameters initialInvariant actual operational returnAdmissible
      finalSubstitutionExtension resultExtension
      (TypingSourceExtends.refl _) rawResultExtension
      integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered
  exact ⟨finalContext, facts, finalInvariant.active, finalActual, finalOperational, typing, agreement⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
