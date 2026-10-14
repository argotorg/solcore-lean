import Solcore.SourceSemantics.SourceInferenceSelectedAttachedChild
import Solcore.SourceSemantics.SourceInferenceSelectedExpressionState
import Solcore.SourceSemantics.SourceInferenceSelectedOperatorRecording
import Solcore.SourceSemantics.SourceInferenceSelectedOperatorMetadata
import Solcore.SourceSemantics.SourceInferenceSelectedCallRecording
import Solcore.SourceSemantics.SourceInferenceSelectedNamedCall

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferExprFuelRetainedSoundness_unary_operator {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression operandExpression : Syntax.Expr} {operator : Syntax.Located Syntax.UnaryOp} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .unary operator operandExpression →
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
    ∀ {allocated operandState : State} {id : ExpressionId}
      {operand : InferredExpression} {operatorResult : Detail.OperatorInferenceResult},
    initial.allocateExpressionId = (id, allocated) →
    Detail.inferExprFuel fuel inferenceContext operandExpression none allocated = .ok (operand, operandState) →
    Detail.inferUnaryOperator inferenceContext operator.value operand.type expected
      (Detail.relevantIntegerLiterals operandState allocated.integerLiterals.length [operand])
      operandState = .ok operatorResult →
    Detail.recordExpressionWithExpected inferenceContext expression id operatorResult.type
      (.unary operator.value operand.id) operatorResult.requirements expected
      operatorResult.state = .ok (inferred, resultState) →
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      semanticContext finalized.substitution inferred := by
  intro wholeContext inferenceContext wholeReturn expression operandExpression operator expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained operatorsRetained childrenRetained covered semanticPreserved actualCovered
    allocated operandState id operand operatorResult allocationEq operandSuccess operatorSuccess recorded
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational := operational.allocateExpressionId allocationEq
  have properties := Detail.inferExprFuel_inferenceProperties allocatedInvariant.ready
    signatureFormation functionsCanonical (by simp) operandSuccess
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]
    exact expectedBelow
  have operandExpected : ∀ type ∈ expected, type.VariablesBelow operandState.inference.next := by
    intro type member
    exact (allocatedExpected type member).weaken properties.1.next_le
  have operatorProperties := Detail.inferUnaryOperator_inferenceProperties
    properties.2.1 properties.2.2 operandExpected operatorSuccess
  have operatorExpected : ∀ type ∈ expected, type.VariablesBelow operatorResult.state.inference.next := by
    intro type member
    exact (operandExpected type member).weaken operatorProperties.1.next_le
  have recording := Detail.recordExpressionWithExpected_inferenceProperties
    operatorProperties.2.1 operatorProperties.2.2 operatorExpected recorded
  have childExtension := resultSubstitutionExtension.trans
    (recording.1.substitution_extends.trans operatorProperties.1.substitution_extends)
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have childToParent : TypingSourceExtends (operandState.toTypedSource roots)
      (resultState.toTypedSource roots) := by
    constructor
    · exact (Detail.inferExprFuel_preserves_owner success).trans
        (allocatedOwner.symm.trans (Detail.inferExprFuel_preserves_owner operandSuccess).symm)
    · change operandState.nodes <+: resultState.nodes
      rw [← (Detail.inferUnaryOperator_occurrenceState_eq operatorSuccess).1]
      exact recordExpressionWithExpected_success_nodesPrefix recorded
  obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded roots
  have edge : DirectChild (resultState.toTypedSource roots)
      (.expression inferred.id) (.expression operand.id) := by
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simp [nodeChildIds, Node.references, ExpressionForm.references]
  have finalEdge := childrenRetained edge
  have childPatterns : operandState.integerPatterns ⊆ evidenceState.integerPatterns := by
    rw [← Detail.SelectedMetadata.inferUnaryOperator_integerPatterns_eq operatorSuccess,
      ← recordExpressionWithExpected_integerPatterns_eq recorded]
    exact integerPatternsSubset
  have childLiterals : operandState.integerLiterals ⊆ evidenceState.integerLiterals := by
    rw [← Detail.SelectedMetadata.inferUnaryOperator_integerLiterals_eq operatorSuccess,
      ← Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact integerLiteralsSubset
  have childRequirements := List.Subset.trans
    (Detail.inferUnaryOperator_requirements_subset operatorSuccess)
    (List.Subset.trans (Detail.recordExpressionWithExpected_requirements_subset recorded) requirementsSubset)
  have typed := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
    operandSuccess resources interfaces childExtension signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical allocatedInvariant actual allocatedOperational
    (by simp) (by simp) ((semanticPreserved.childSubtree edge).monoBefore childToParent)
    ((finalPreserved.childSubtree edge).monoBefore childToParent)
    ((rawProper.childSubtree edge).monoBefore childToParent).proper childPatterns childLiterals childRequirements
    (covered.expressionChild resources.graph_closed finalEdge) (actualCovered.directChild finalEdge)
  have activeSignatures : semanticContext.signatures = inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed semanticContext.signatures := by
    rw [activeSignatures]; exact catalog
  have wholeCanonical : SignatureParametersWellFormed wholeContext.scope.genericOwner wholeContext.typeParameters := by
    simpa only [ownerEq, typeParametersEq] using canonical
  have finalSubstitution := resources.substitution_eq.symm
  have finalRequirements : resultState.requirements ⊆ resources.finalState.requirements := by
    rw [resources.requirements_eq]; exact requirementsSubset
  have targets : ∀ origin ∈ Detail.relevantIntegerLiterals operandState allocated.integerLiterals.length [operand],
      resources.finalState.inference.substitution.apply (.variable origin.metavariable) = .word ∨
      resources.finalState.inference.substitution.apply (.variable origin.metavariable) = .integer := by
    intro origin member
    have present : origin ∈ operandState.integerLiterals := by
      unfold Detail.relevantIntegerLiterals at member
      exact (List.mem_filter.mp member).1
    simpa only [finalSubstitution] using resources.integer_literal_target_supported origin (childLiterals present)
  simpa only [finalSubstitution] using
    (inferUnaryOperator_recordExpressionWithExpected_typing_from_interfaces
      (later := resources.finalState) (base := finalizedRequirementContext wholeContext finalized)
      operatorSuccess recorded (by simpa only [finalSubstitution] using typed)
      properties.2.1 properties.2.2 operandExpected targets
      (by simpa only [finalSubstitution] using resultSubstitutionExtension)
      finalRequirements retained (by simpa only [signaturesEq] using interfaces) coercionsRetained operatorsRetained
      activeCatalog (invariant.typeParameterBinders wholeCanonical) activeSignatures
      resources.solve_success resources.solved_context_eq resources.ledger resources.ownership
      invariant.signaturesEq invariant.solvedRequirementsEq invariant.assumptionsMono covered)

theorem actualInferExprFuelRetainedSoundness_unary {fuel : Nat}
    (recursive : ∀ smaller, smaller < fuel + 1 → ActualInferExprFuelRetainedSoundness smaller) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression operandExpression : Syntax.Expr} {operator : Syntax.Located Syntax.UnaryOp} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .unary operator operandExpression →
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
  intro wholeContext inferenceContext wholeReturn expression operandExpression operator expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained operatorsRetained childrenRetained covered semanticPreserved actualCovered
  generalize allocationEq : initial.allocateExpressionId = pair
  obtain ⟨id, allocated⟩ := pair
  obtain ⟨operand, operandState, operandSuccess, dispatch⟩ :=
    Detail.inferExprFuel_success_unary_facts expressionEq allocationEq success
  cases dispatch with
  | directFunction dispatch lookup operatorSuccess recorded =>
      exact actualInferExprFuelRetainedSoundness_unary_operator (recursive fuel (Nat.lt_succ_self _))
        expressionEq success resources interfaces resultSubstitutionExtension signaturesEq ownerEq typeParametersEq
        assumptionsEq signatureFormation functionsCanonical catalog canonical invariant actual operational
        expectedBelow expectedAdmissible finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
        retained coercionsRetained operatorsRetained childrenRetained covered semanticPreserved actualCovered
        allocationEq operandSuccess operatorSuccess recorded
  | traitMethod dispatch operatorSuccess recorded =>
      exact actualInferExprFuelRetainedSoundness_unary_operator (recursive fuel (Nat.lt_succ_self _))
        expressionEq success resources interfaces resultSubstitutionExtension signaturesEq ownerEq typeParametersEq
        assumptionsEq signatureFormation functionsCanonical catalog canonical invariant actual operational
        expectedBelow expectedAdmissible finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
        retained coercionsRetained operatorsRetained childrenRetained covered semanticPreserved actualCovered
        allocationEq operandSuccess operatorSuccess recorded
  | selectedFunction dispatch lookup selected recorded =>
      have argumentsSuccess : Detail.inferExprsFuel (fuel + 1) inferenceContext [operandExpression] allocated =
          .ok ([operand], operandState) := by
        cases fuel with
        | zero => simp [Detail.inferExprFuel] at operandSuccess
        | succ fuel => simp [Detail.inferExprsFuel, operandSuccess, bind, Except.bind, pure, Except.pure]
      exact actualSelectedCall_typing recursive argumentsSuccess selected recorded
        (Detail.functionsNamed_success_subset_catalog lookup) resources interfaces resultSubstitutionExtension
        signaturesEq ownerEq typeParametersEq assumptionsEq signatureFormation functionsCanonical catalog canonical
        (invariant.allocateExpressionId allocationEq) actual (operational.allocateExpressionId allocationEq)
        (by simpa only [allocateExpressionId_inferenceNext_eq allocationEq] using expectedBelow)
        expectedAdmissible finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
        retained coercionsRetained operatorsRetained childrenRetained covered semanticPreserved actualCovered

end Solcore.SourceSemantics.SourceInferenceSoundness
