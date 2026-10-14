import Solcore.SourceSemantics.SourceInferenceSelectedExpressionList
import Solcore.SourceSemantics.SourceInferenceSelectedOrdinaryRecorder

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferExprFuelRetainedSoundness_tuple {fuel : Nat}
    (recursive : ∀ smaller, smaller < fuel + 1 → ActualInferExprFuelRetainedSoundness smaller) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression : Syntax.Expr} {elements : Syntax.DelimitedList Syntax.Expr} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .tuple elements →
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
  intro wholeContext inferenceContext wholeReturn expression elements expected initial
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
    refine ⟨⟨pending, ?_⟩, ?_, ?_⟩
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
  obtain ⟨elementsResult, elementsState, elementsSuccess, recorded⟩ :=
    Detail.inferExprFuel_success_tuple_facts expressionEq allocationEq success
  have properties := Detail.inferExprsFuel_inferenceProperties allocatedInvariant.ready
    signatureFormation functionsCanonical elementsSuccess
  have elementsExpected : ∀ type ∈ expected, type.VariablesBelow elementsState.inference.next := by
    intro type member
    exact (allocatedExpected type member).weaken properties.1.next_le
  have rawBelow : (Ty.productMany (elementsResult.map (·.type))).VariablesBelow elementsState.inference.next :=
    Ty.variablesBelow_productMany (by
      intro type member
      obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
      exact properties.2.2 element elementMember)
  have recording := Detail.recordExpressionWithExpected_inferenceProperties
    properties.2.1 rawBelow elementsExpected recorded
  have elementsExtension := resultSubstitutionExtension.trans recording.1.substitution_extends
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have allocatedToElements := inferExprsFuel_success_typingSourceExtends_under_bound
    elementsSuccess allocatedInvariant.nodesBelow roots
  have elementsToParent : TypingSourceExtends (elementsState.toTypedSource roots)
      (resultState.toTypedSource roots) := by
    refine ⟨?_, recordExpressionWithExpected_success_nodesPrefix recorded⟩
    exact (Detail.inferExprFuel_preserves_owner success).trans
      (allocatedOwner.symm.trans allocatedToElements.owner_eq.symm)
  obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded roots
  have edge : ∀ element ∈ elementsResult, DirectChild (resultState.toTypedSource roots)
      (.expression inferred.id) (.expression element.id) := by
    intro element member
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simpa [nodeChildIds, Node.references, ExpressionForm.references] using
      (List.mem_map.mpr ⟨element.id, List.mem_map.mpr ⟨element, member, rfl⟩, rfl⟩ :
        NodeId.expression element.id ∈ (elementsResult.map (·.id)).map NodeId.expression)
  have childPatterns : elementsState.integerPatterns ⊆ evidenceState.integerPatterns := by
    rw [← recordExpressionWithExpected_integerPatterns_eq recorded]
    exact integerPatternsSubset
  have childLiterals : elementsState.integerLiterals ⊆ evidenceState.integerLiterals := by
    rw [← Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact integerLiteralsSubset
  have childRequirements := List.Subset.trans
    (Detail.recordExpressionWithExpected_requirements_subset recorded) requirementsSubset
  have typed := actualInferExprsFuelFinalSubtreeSoundness fuel
    (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self fuel)))
    elementsSuccess resources interfaces elementsExtension signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical allocatedInvariant actual allocatedOperational
    (fun element member => (semanticPreserved.childSubtree (edge element member)).monoBefore elementsToParent)
    (fun element member => (finalPreserved.childSubtree (edge element member)).monoBefore elementsToParent)
    (fun element member => ((rawProper.childSubtree (edge element member)).monoBefore elementsToParent).proper)
    childPatterns childLiterals childRequirements
    (fun element member => covered.expressionChild resources.graph_closed (childrenRetained (edge element member)))
    (fun element member => actualCovered.directChild (childrenRetained (edge element member)))
  have formType : ExpressionFormHasRawType semanticSource semanticContext
      ((ExpressionForm.tuple (elementsResult.map (·.id))).applySubstitution finalized.substitution)
      (finalized.substitution.apply (Ty.productMany (elementsResult.map (·.type)))) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution, FlexibleSubstitution.apply_productMany,
      List.map_map, Function.comp_def] using ExpressionFormHasRawType.tuple typed
  have rawAdmissible : TypeAdmissible semanticContext
      (finalized.substitution.apply (Ty.productMany (elementsResult.map (·.type)))) := by
    simpa [FlexibleSubstitution.apply_productMany, List.map_map, Function.comp_def] using
      typed.product_type_admissible (invariant.typeParameterBinders (by
        simpa [ownerEq, typeParametersEq] using canonical))
  exact recordExpressionWithExpected_success_expressionTypingBase_actual resources interfaces
    recorded resultSubstitutionExtension requirementsSubset retained coercionsRetained
    catalog signaturesEq invariant formType rawAdmissible covered

end Solcore.SourceSemantics.SourceInferenceSoundness
