import Solcore.SourceSemantics.SourceInferenceSelectedChildSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedOrdinaryRecorder

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferExprFuelRetainedSoundness_group {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression inner : Syntax.Expr} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .group inner →
    Detail.inferExprFuel (fuel + 1) inferenceContext expression expected initial =
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
    ProperDescendantsPreserved finalized.substitution
      (resultState.toTypedSource roots) finalized.typedSource
      (.expression inferred.id) →
    RawProperDescendantsPreserved (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.expression inferred.id) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionOperatorSiteRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionDirectChildrenRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.expression inferred.id) →
    ProperDescendantsPreserved finalized.substitution (resultState.toTypedSource roots)
      semanticSource (.expression inferred.id) →
    ActualContext.Covers finalized frames (.expression inferred.id) →
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      semanticContext finalized.substitution inferred := by
  intro wholeContext inferenceContext wholeReturn expression inner expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained _operatorsRetained childrenRetained covered semanticPreserved actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational : ActualStateInvariant allocated (evidenceState.toTypedSource roots) := by
    obtain ⟨pending, ledger⟩ := operational.ledger
    have stateEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
    refine ⟨⟨pending, ?_⟩, ?_, ?_, operational.sourceMonomorphic⟩
    · rw [← stateEq]
      exact ledger.allocateExpressionId
    · apply operational.origins.congr_localBinders
      rw [← stateEq]
      rfl
    · apply activeQuantifiersBelowNext_transport operational.quantifiersBelow
      · rw [← stateEq]; rfl
      · rw [← stateEq]; exact Nat.le_refl _
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]
    exact expectedBelow
  obtain ⟨innerResult, innerState, innerSuccess, recorded⟩ :=
    Detail.inferExprFuel_success_group_facts expressionEq allocationEq success
  have properties := Detail.inferExprFuel_inferenceProperties allocatedInvariant.ready
    signatureFormation functionsCanonical allocatedExpected innerSuccess
  have innerExpected : ∀ type ∈ expected, type.VariablesBelow innerState.inference.next := by
    intro type member
    exact (allocatedExpected type member).weaken properties.1.next_le
  have recording := Detail.recordExpressionWithExpected_inferenceProperties
    properties.2.1 properties.2.2 innerExpected recorded
  have innerExtension := resultSubstitutionExtension.trans recording.1.substitution_extends
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have innerToParent : TypingSourceExtends (innerState.toTypedSource roots)
      (resultState.toTypedSource roots) := by
    refine ⟨?_, recordExpressionWithExpected_success_nodesPrefix recorded⟩
    exact (Detail.inferExprFuel_preserves_owner success).trans
      (allocatedOwner.symm.trans (Detail.inferExprFuel_preserves_owner innerSuccess).symm)
  obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded roots
  have edge : DirectChild (resultState.toTypedSource roots)
      (.expression inferred.id) (.expression innerResult.id) := by
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simp [nodeChildIds, Node.references, ExpressionForm.references]
  have finalEdge := childrenRetained edge
  have childFinal := (finalPreserved.childSubtree edge).monoBefore innerToParent
  have childSemantic := (semanticPreserved.childSubtree edge).monoBefore innerToParent
  have childPatterns : innerState.integerPatterns ⊆ evidenceState.integerPatterns := by
    rw [← recordExpressionWithExpected_integerPatterns_eq recorded]
    exact integerPatternsSubset
  have childLiterals : innerState.integerLiterals ⊆ evidenceState.integerLiterals := by
    rw [← Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact integerLiteralsSubset
  have childRequirements := List.Subset.trans
    (Detail.recordExpressionWithExpected_requirements_subset recorded) requirementsSubset
  have typed := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
    innerSuccess resources interfaces innerExtension signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical allocatedInvariant actual allocatedOperational
    allocatedExpected expectedAdmissible childSemantic childFinal
    ((rawProper.childSubtree edge).monoBefore innerToParent).proper childPatterns childLiterals childRequirements
    (covered.expressionChild resources.graph_closed finalEdge) (actualCovered.directChild finalEdge)
  have formType : ExpressionFormHasRawType semanticSource semanticContext
      ((ExpressionForm.group innerResult.id).applySubstitution finalized.substitution)
      (finalized.substitution.apply innerResult.type) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution] using ExpressionFormHasRawType.group typed
  exact recordExpressionWithExpected_success_expressionTypingBase_actual resources interfaces
    recorded resultSubstitutionExtension requirementsSubset retained coercionsRetained
    catalog signaturesEq invariant formType typed.type_admissible covered

end Solcore.SourceSemantics.SourceInferenceSoundness
