import Solcore.SourceSemantics.SourceInferenceActualRootedContracts

/-! Recursive child typing only needs the selected occurrence subtree in the
final evidence and the semantic carrier. Earlier sibling roots may differ. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem ProperDescendantsPreserved.childSubtree
    {substitution : Substitution} {before after : TypedSource} {root child : NodeId}
    (preserved : ProperDescendantsPreserved substitution before after root)
    (edge : DirectChild before root child) : SubtreePreserved substitution before after child := by
  refine ⟨preserved.owner_eq, ?_⟩
  intro node member path
  exact preserved.nodes node member
    (path.elim (fun same => same ▸ Descends.direct edge) (fun path => .step edge path))

theorem FinalInferenceResources.finalExpressionTypeAdmissible_in_active
    {wholeContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    {node : ExpressionNode} {id : ExpressionId} {active : SourceSemantics.Context}
    (contains : ContainsExpression finalized.typedSource id node)
    (binders : TypeParameterBindersWellFormed active)
    (signaturesEq : active.signatures = wholeContext.signatures)
    (parametersEq : active.typeParameters = wholeContext.typeParameters)
    (ownerEq : active.currentDeclaration = some wholeContext.scope.genericOwner)
    (residual : active.residualTypeVariables = true) :
    TypeAdmissible active node.type := by
  have member := contains.1
  rw [resources.source_eq] at member
  obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
  cases original with
  | expression original =>
    have sameNode : original.applySubstitution finalized.substitution = node := Node.expression.inj same
    rw [← sameNode]
    exact resources.expressionTypeAdmissible_in_active originalMember
      binders signaturesEq parametersEq ownerEq residual
  | statement original => cases same

def ActualInferExprFuelFinalSubtreeSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    Detail.inferExprFuel fuel inferenceContext expression expected initial =
        .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
    finalized.substitution.SemanticallyExtends
      resultState.inference.substitution →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next) →
    (∀ expectedType ∈ expected,
      TypeAdmissible semanticContext (finalized.substitution.apply expectedType)) →
    SubtreePreserved finalized.substitution
      (resultState.toTypedSource roots) semanticSource (.expression inferred.id) →
    SubtreePreserved finalized.substitution (resultState.toTypedSource roots)
      finalized.typedSource (.expression inferred.id) →
    RawProperDescendantsPreserved (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.expression inferred.id) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.expression inferred.id) →
    ActualContext.Covers finalized frames (.expression inferred.id) →
    ExpressionHasType semanticSource semanticContext inferred.id
      (finalized.substitution.apply inferred.type)

theorem actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness
    {fuel : Nat} (retainedSound : ActualInferExprFuelRetainedSoundness fuel) :
    ActualInferExprFuelFinalSubtreeSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expression expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    resultPreserved finalPreserved rawProper integerPatternsSubset
    integerLiteralsSubset requirementsSubset covered actualCovered
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
    finalPreserved.proper rawProper integerPatternsSubset integerLiteralsSubset
    requirementsSubset requirementsRetained
    (ExpressionCoercionPrimariesRetainedAt.ofExpressionNodesPreservedAt finalized.substitution finalNodes)
    (ExpressionOperatorSiteRetainedAt.ofExpressionNodesPreservedAt finalized.substitution finalNodes)
    childrenRetained covered
    resultPreserved.proper actualCovered
  cases base with
  | @intro node rawType plan contains typeEq formType rawAdmissible requirements =>
      have finalContains := finalNodes (by simp)
        (FlexibleSubstitution.ContainsExpression.applySubstitution finalized.substitution contains)
      have finalAdmissible : TypeAdmissible semanticContext
          (finalized.substitution.apply inferred.type) := by
        have nodeAdmissible := resources.finalExpressionTypeAdmissible_in_active
          finalContains
          (invariant.typeParameterBinders (by
            simpa [ownerEq, typeParametersEq] using canonical))
          invariant.signatures_eq_whole invariant.typeParametersEq
          invariant.declarationEq invariant.residual
        simpa only [ExpressionNode.applySubstitution, typeEq] using nodeAdmissible
      have semanticNodes : ExpressionNodesPreservedAt [inferred.id]
          ((resultState.toTypedSource roots).applySubstitution finalized.substitution)
          semanticSource := by
        intro id selected member found
        have same : id = inferred.id := by simpa using member
        subst id
        exact resultPreserved.subgraph.containsExpression found (.inl rfl)
      exact (ExpressionTypingBase.intro contains typeEq formType rawAdmissible requirements
        ).expressionHasType semanticNodes finalAdmissible


end Solcore.SourceSemantics.SourceInferenceSoundness
