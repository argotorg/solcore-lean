import Solcore.SourceSemantics.SourceInferenceActualRootedContracts

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualInferExprFuelRootedSoundness_of_retainedSoundness
    {fuel : Nat} (retainedSound : ActualInferExprFuelRetainedSoundness fuel) :
    ActualInferExprFuelRootedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expression expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    resultPreserved rawPreserved integerPatternsSubset
    integerLiteralsSubset requirementsSubset covered actualCovered
  have finalPreserved : SubtreePreserved finalized.substitution
      (resultState.toTypedSource roots) finalized.typedSource (.expression inferred.id) := by
    rw [resources.source_eq]
    exact rawPreserved.substituted finalized.substitution
  have finalNodes : ExpressionNodesPreservedAt [inferred.id]
      ((resultState.toTypedSource roots).applySubstitution finalized.substitution)
      finalized.typedSource := by
    intro id node member contains
    have same : id = inferred.id := by simpa using member
    subst id
    exact finalPreserved.subgraph.containsExpression contains (.inl rfl)
  have requirementsRetained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id := by
    intro node requirement contains member
    have found := finalNodes (by simp)
      (FlexibleSubstitution.ContainsExpression.applySubstitution finalized.substitution contains)
    apply found.primaryRequirementOccursAt
    simpa [ExpressionNode.applySubstitution] using member
  have childrenRetained : ExpressionDirectChildrenRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id :=
    ExpressionDirectChildrenRetainedAt.ofExpressionNodesPreservedAt finalNodes
  have base := retainedSound success resources interfaces resultSubstitutionExtension
    signaturesEq ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved.proper rawPreserved.proper integerPatternsSubset integerLiteralsSubset
    requirementsSubset requirementsRetained
    (ExpressionCoercionPrimariesRetainedAt.ofExpressionNodesPreservedAt finalized.substitution finalNodes)
    (ExpressionOperatorSiteRetainedAt.ofExpressionNodesPreservedAt finalized.substitution finalNodes)
    childrenRetained covered
    resultPreserved.proper actualCovered
  cases base with
  | @intro node rawType plan contains typeEq formType rawAdmissible requirements =>
      have evidenceMember : Node.expression node ∈
          (evidenceState.toTypedSource roots).nodes :=
        rawPreserved.nodes (.expression node) contains.1
          (.inl (congrArg NodeId.expression contains.2))
      have finalAdmissible : TypeAdmissible semanticContext
          (finalized.substitution.apply inferred.type) := by
        have nodeAdmissible := resources.expressionTypeAdmissible_in_active
          evidenceMember
          (invariant.typeParameterBinders (by
            simpa [ownerEq, typeParametersEq] using canonical))
          invariant.signatures_eq_whole invariant.typeParametersEq
          invariant.declarationEq invariant.residual
        simpa only [typeEq] using nodeAdmissible
      have semanticNodes : ExpressionNodesPreservedAt [inferred.id]
          ((resultState.toTypedSource roots).applySubstitution finalized.substitution)
          semanticSource := by
        intro id selected member found
        have same : id = inferred.id := by simpa using member
        subst id
        exact resultPreserved.subgraph.containsExpression found (.inl rfl)
      exact (ExpressionTypingBase.intro contains typeEq formType rawAdmissible requirements
        ).expressionHasType semanticNodes finalAdmissible

theorem actualInferExprFuelScopedSoundness_of_rootedSoundness
    {fuel : Nat} (rooted : ActualInferExprFuelRootedSoundness fuel) :
    ActualInferExprFuelScopedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expression expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    resultExtension _ rawExtension integerPatternsSubset
    integerLiteralsSubset requirementsSubset covered actualCovered
  exact rooted success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    (SubtreePreserved.ofTypingSourceExtends resultExtension)
    (RawSubtreePreserved.ofTypingSourceExtends rawExtension)
    integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered

theorem actualInferStatementFuelScopedSoundness_of_rootedSoundness
    {fuel : Nat} (rooted : ActualInferStatementFuelRootedSoundness fuel) :
    ActualInferStatementFuelScopedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement
    initial result evidenceState roots finalized semanticSource frames semanticContext
    success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical catalog signatureParameters
    invariant actual operational returnAdmissible substitutionExtension resultExtension _ rawExtension
    integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered
  exact rooted success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical catalog signatureParameters invariant actual operational returnAdmissible
    substitutionExtension (SubtreePreserved.ofTypingSourceExtends resultExtension)
    (RawSubtreePreserved.ofTypingSourceExtends rawExtension)
    integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered

theorem actualInferStatementsFuelScopedSoundness_of_rootedSoundness
    {fuel : Nat} (rooted : ActualInferStatementsFuelRootedSoundness fuel) :
    ActualInferStatementsFuelScopedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statements
    initial result evidenceState roots finalized semanticSource frames semanticContext
    success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical catalog signatureParameters
    invariant actual operational returnAdmissible substitutionExtension resultExtension _ rawExtension
    integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered
  exact rooted success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical catalog signatureParameters invariant actual operational returnAdmissible
    substitutionExtension (fun _ _ => SubtreePreserved.ofTypingSourceExtends resultExtension)
    (fun _ _ => RawSubtreePreserved.ofTypingSourceExtends rawExtension)
    integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered

end Solcore.SourceSemantics.SourceInferenceSoundness
