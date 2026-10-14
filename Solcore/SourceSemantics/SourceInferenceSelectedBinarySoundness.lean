import Solcore.SourceSemantics.SourceInferenceSelectedAttachedChild
import Solcore.SourceSemantics.SourceInferenceSelectedExpressionState
import Solcore.SourceSemantics.SourceInferenceSelectedOperatorRecording
import Solcore.SourceSemantics.SourceInferenceSelectedOperatorMetadata
import Solcore.SourceSemantics.SourceInferenceSelectedCallRecording

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferExprFuelRetainedSoundness_binary_operator {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression leftExpression rightExpression : Syntax.Expr} {operator : Syntax.Located Syntax.BinaryOp} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .binary leftExpression operator rightExpression →
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
    ∀ {allocated leftState rightState : State} {id : ExpressionId}
      {left right : InferredExpression} {operatorResult : Detail.OperatorInferenceResult},
    initial.allocateExpressionId = (id, allocated) →
    Detail.inferExprFuel fuel inferenceContext leftExpression none allocated = .ok (left, leftState) →
    Detail.inferExprFuel fuel inferenceContext rightExpression none leftState = .ok (right, rightState) →
    Detail.inferBinaryOperator inferenceContext operator.value left.type right.type expected
      (Detail.relevantIntegerLiterals rightState allocated.integerLiterals.length [left, right])
      rightState = .ok operatorResult →
    Detail.recordExpressionWithExpected inferenceContext expression id operatorResult.type
      (.binary left.id operator.value right.id) operatorResult.requirements expected
      operatorResult.state = .ok (inferred, resultState) →
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      semanticContext finalized.substitution inferred := by
  intro wholeContext inferenceContext wholeReturn expression leftExpression rightExpression operator expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained operatorsRetained childrenRetained covered semanticPreserved actualCovered
    allocated leftState rightState id left right operatorResult allocationEq leftSuccess rightSuccess operatorSuccess recorded
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational := operational.allocateExpressionId allocationEq
  have leftProperties := Detail.inferExprFuel_inferenceProperties allocatedInvariant.ready
    signatureFormation functionsCanonical (by simp) leftSuccess
  have rightProperties := Detail.inferExprFuel_inferenceProperties leftProperties.2.1
    signatureFormation functionsCanonical (by simp) rightSuccess
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]
    exact expectedBelow
  have rightExpected : ∀ type ∈ expected, type.VariablesBelow rightState.inference.next := by
    intro type member
    exact (allocatedExpected type member).weaken (Nat.le_trans leftProperties.1.next_le rightProperties.1.next_le)
  have leftBelow := leftProperties.2.2.weaken rightProperties.1.next_le
  have operatorProperties := Detail.inferBinaryOperator_inferenceProperties
    rightProperties.2.1 leftBelow rightProperties.2.2 rightExpected operatorSuccess
  have operatorExpected : ∀ type ∈ expected, type.VariablesBelow operatorResult.state.inference.next := by
    intro type member
    exact (rightExpected type member).weaken operatorProperties.1.next_le
  have recording := Detail.recordExpressionWithExpected_inferenceProperties
    operatorProperties.2.1 operatorProperties.2.2 operatorExpected recorded
  have rightExtension := resultSubstitutionExtension.trans
    (recording.1.substitution_extends.trans operatorProperties.1.substitution_extends)
  have leftExtension := rightExtension.trans rightProperties.1.substitution_extends
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have rightToParent : TypingSourceExtends (rightState.toTypedSource roots)
      (resultState.toTypedSource roots) := by
    constructor
    · exact (Detail.inferExprFuel_preserves_owner success).trans
        (allocatedOwner.symm.trans ((Detail.inferExprFuel_preserves_owner leftSuccess).symm.trans
          (Detail.inferExprFuel_preserves_owner rightSuccess).symm))
    · change rightState.nodes <+: resultState.nodes
      rw [← (Detail.inferBinaryOperator_occurrenceState_eq operatorSuccess).1]
      exact recordExpressionWithExpected_success_nodesPrefix recorded
  have leftNodes := (Detail.inferExprFuel_occurrenceBoundExtends leftSuccess).nodesBelowNextOccurrence allocatedInvariant.nodesBelow
  have leftToRight := inferExprFuel_success_typingSourceExtends rightSuccess leftNodes roots
  have leftToParent := leftToRight.trans rightToParent
  obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded roots
  have leftEdge : DirectChild (resultState.toTypedSource roots)
      (.expression inferred.id) (.expression left.id) := by
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simp [nodeChildIds, Node.references, ExpressionForm.references]
  have rightEdge : DirectChild (resultState.toTypedSource roots)
      (.expression inferred.id) (.expression right.id) := by
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simp [nodeChildIds, Node.references, ExpressionForm.references]
  have rightPatterns : rightState.integerPatterns ⊆ evidenceState.integerPatterns := by
    rw [← Detail.SelectedMetadata.inferBinaryOperator_integerPatterns_eq operatorSuccess,
      ← recordExpressionWithExpected_integerPatterns_eq recorded]
    exact integerPatternsSubset
  have rightLiterals : rightState.integerLiterals ⊆ evidenceState.integerLiterals := by
    rw [← Detail.SelectedMetadata.inferBinaryOperator_integerLiterals_eq operatorSuccess,
      ← Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact integerLiteralsSubset
  have rightRequirements := List.Subset.trans
    (Detail.inferBinaryOperator_requirements_subset operatorSuccess)
    (List.Subset.trans (Detail.recordExpressionWithExpected_requirements_subset recorded) requirementsSubset)
  have leftTyped := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
    leftSuccess resources interfaces leftExtension signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical allocatedInvariant actual allocatedOperational
    (by simp) (by simp) ((semanticPreserved.childSubtree leftEdge).monoBefore leftToParent)
    ((finalPreserved.childSubtree leftEdge).monoBefore leftToParent)
    ((rawProper.childSubtree leftEdge).monoBefore leftToParent).proper
    ((Detail.inferExprFuel_integerPatterns_subset rightSuccess).trans rightPatterns)
    ((Detail.inferExprFuel_integerLiterals_subset rightSuccess).trans rightLiterals)
    ((Detail.inferExprFuel_requirements_subset rightSuccess).trans rightRequirements)
    (covered.expressionChild resources.graph_closed (childrenRetained leftEdge))
    (actualCovered.directChild (childrenRetained leftEdge))
  have leftInvariant := allocatedInvariant.ofExpression signatureFormation functionsCanonical (by simp) leftExtension leftSuccess
  have leftOperational := allocatedOperational.ofExpression leftSuccess leftProperties.1.next_le
  have rightTyped := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
    rightSuccess resources interfaces rightExtension signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical leftInvariant actual leftOperational
    (by simp) (by simp) ((semanticPreserved.childSubtree rightEdge).monoBefore rightToParent)
    ((finalPreserved.childSubtree rightEdge).monoBefore rightToParent)
    ((rawProper.childSubtree rightEdge).monoBefore rightToParent).proper rightPatterns rightLiterals rightRequirements
    (covered.expressionChild resources.graph_closed (childrenRetained rightEdge))
    (actualCovered.directChild (childrenRetained rightEdge))
  have activeSignatures : semanticContext.signatures = inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed semanticContext.signatures := by
    rw [activeSignatures]; exact catalog
  have wholeCanonical : SignatureParametersWellFormed wholeContext.scope.genericOwner wholeContext.typeParameters := by
    simpa only [ownerEq, typeParametersEq] using canonical
  have finalSubstitution := resources.substitution_eq.symm
  have finalRequirements : resultState.requirements ⊆ resources.finalState.requirements := by
    rw [resources.requirements_eq]; exact requirementsSubset
  have targets : ∀ origin ∈ Detail.relevantIntegerLiterals rightState allocated.integerLiterals.length [left, right],
      resources.finalState.inference.substitution.apply (.variable origin.metavariable) = .word ∨
      resources.finalState.inference.substitution.apply (.variable origin.metavariable) = .integer := by
    intro origin member
    have present : origin ∈ rightState.integerLiterals := (List.mem_filter.mp member).1
    simpa only [finalSubstitution] using resources.integer_literal_target_supported origin (rightLiterals present)
  simpa only [finalSubstitution] using
    (inferBinaryOperator_recordExpressionWithExpected_typing_from_interfaces
      (later := resources.finalState) (base := finalizedRequirementContext wholeContext finalized)
      operatorSuccess recorded (by simpa only [finalSubstitution] using leftTyped)
      (by simpa only [finalSubstitution] using rightTyped)
      rightProperties.2.1 leftBelow rightProperties.2.2 rightExpected targets
      (by simpa only [finalSubstitution] using resultSubstitutionExtension)
      finalRequirements retained (by simpa only [signaturesEq] using interfaces) coercionsRetained operatorsRetained
      activeCatalog (invariant.typeParameterBinders wholeCanonical) activeSignatures
      resources.solve_success resources.solved_context_eq resources.ledger resources.ownership
      invariant.signaturesEq invariant.solvedRequirementsEq invariant.assumptionsMono covered)

theorem actualInferExprFuelRetainedSoundness_binary_selected {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression leftExpression rightExpression : Syntax.Expr} {operator : Syntax.Located Syntax.BinaryOp} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .binary leftExpression operator rightExpression →
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
    ∀ {allocated leftState rightState : State} {id : ExpressionId}
      {left right : InferredExpression} {name : String} {candidates : List ProgramFunctionSignature}
      {attempt : Detail.CandidateAttemptResult} {fitted : Detail.ExpectationResult} {callee : Syntax.Expr},
    initial.allocateExpressionId = (id, allocated) →
    Detail.inferExprFuel fuel inferenceContext leftExpression none allocated = .ok (left, leftState) →
    Detail.inferExprFuel fuel inferenceContext rightExpression none leftState = .ok (right, rightState) →
    Detail.selectFunctionCandidateFrom inferenceContext name candidates [left, right]
      (Detail.relevantIntegerLiterals rightState allocated.integerLiterals.length [left, right])
      id (some .bool) rightState = .ok attempt →
    Detail.withExpected inferenceContext attempt.state attempt.result expected = .ok fitted →
    Detail.recordSelectedCallResult expression callee name [left, right] attempt
      fitted.expression fitted.coercions fitted.state = (inferred, resultState) →
    candidates ⊆ inferenceContext.signatures.functions →
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      semanticContext finalized.substitution inferred := by
  intro wholeContext inferenceContext wholeReturn expression leftExpression rightExpression operator expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained operatorsRetained childrenRetained covered semanticPreserved actualCovered
    allocated leftState rightState id left right name candidates attempt fitted callee allocationEq
    leftSuccess rightSuccess selectionSuccess fitting recordSuccess candidatesSubset
  have inferredEq : inferred = fitted.expression := (Detail.recordSelectedCallResult_success_nodes recordSuccess).1
  subst inferred
  have resultIdEq := Detail.withExpected_success_expression_id fitting
  have activeSignaturesEq := invariant.signatures_eq_whole.trans signaturesEq.symm
  obtain ⟨signature, _, signatureMember, signatureCanonical, schemeBelow, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_semanticCandidate signatureFormation functionsCanonical
      activeSignaturesEq candidatesSubset selectionSuccess
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational := operational.allocateExpressionId allocationEq
  have leftProperties := Detail.inferExprFuel_inferenceProperties allocatedInvariant.ready
    signatureFormation functionsCanonical (by simp) leftSuccess
  have rightProperties := Detail.inferExprFuel_inferenceProperties leftProperties.2.1
    signatureFormation functionsCanonical (by simp) rightSuccess
  have argumentsBelow : ∀ argument ∈ [left, right], argument.type.VariablesBelow rightState.inference.next := by
    intro argument member
    rcases List.mem_cons.mp member with rfl | member
    · exact leftProperties.2.2.weaken rightProperties.1.next_le
    · have same : argument = right := List.mem_singleton.mp member
      simpa only [same] using rightProperties.2.2
  have boolBelow : ∀ type ∈ (some Ty.bool), type.VariablesBelow rightState.inference.next := by
    intro type member
    have same : type = .bool := by simpa only [Option.mem_def, Option.some.injEq] using member.symm
    subst type
    exact Ty.variablesBelow_constructor _ _
  have candidateProperties := Detail.tryFunctionCandidate_some_inferenceProperties
    rightProperties.2.1 argumentsBelow schemeBelow boolBelow candidateSuccess
  have expectedAtAttempt : ∀ type ∈ expected, type.VariablesBelow attempt.state.inference.next := by
    intro type member
    have allocatedExpected : type.VariablesBelow allocated.inference.next := by
      rw [allocateExpressionId_inferenceNext_eq allocationEq]
      exact expectedBelow type member
    exact allocatedExpected.weaken (Nat.le_trans leftProperties.1.next_le
      (Nat.le_trans rightProperties.1.next_le candidateProperties.1.next_le))
  have fittingProperties := Detail.withExpected_inferenceProperties candidateProperties.2.1
    candidateProperties.2.2 expectedAtAttempt fitting
  have recordProperties := Detail.recordSelectedCallResult_inferenceProperties expression callee name
    [left, right] attempt fitted.expression fitted.coercions fitted.state fittingProperties.2.1 fittingProperties.2.2
  rw [recordSuccess] at recordProperties
  have fittedExtension := resultSubstitutionExtension.trans recordProperties.1.substitution_extends
  have attemptExtension := fittedExtension.trans fittingProperties.1.substitution_extends
  have rightExtension := attemptExtension.trans candidateProperties.1.substitution_extends
  have leftExtension := rightExtension.trans rightProperties.1.substitution_extends
  have argumentIdsUnique : ([left, right].map (·.id)).Nodup := by
    have leftIndex := Detail.inferExprFuel_success_id_index leftSuccess
    have rightIndex := Detail.inferExprFuel_success_id_index rightSuccess
    have growth := Detail.inferExprFuel_nextOccurrence_lt leftSuccess
    have distinct : left.id ≠ right.id := by
      intro same
      have equalIndex := congrArg (fun id : ExpressionId => id.occurrence.index) same
      rw [leftIndex, rightIndex] at equalIndex
      exact Nat.ne_of_lt growth equalIndex
    simpa using distinct
  have entryIds : attempt.argumentCoercions.map (·.expression) = [left, right].map (·.id) :=
    Detail.tryFunctionCandidate_some_argumentCoercion_expression_ids signatureCanonical candidateSuccess
  have entryIdsUnique : (attempt.argumentCoercions.map (·.expression)).Nodup := by
    rw [entryIds]; exact argumentIdsUnique
  have rightToFitted : TypingSourceExtends (rightState.toTypedSource roots)
      (fitted.state.toTypedSource roots) := by
    refine ⟨?_, ?_⟩
    · exact (congrArg State.Header.owner (Detail.SelectedMetadata.withExpected_state_header fitting)).trans
        (congrArg State.Header.owner (Detail.SelectedMetadata.tryFunctionCandidate_some_state_header candidateSuccess))
    · change rightState.nodes <+: fitted.state.nodes
      rw [(Detail.withExpected_occurrenceState_eq fitting).1,
        (Detail.tryFunctionCandidate_some_occurrenceState_eq candidateSuccess).1]
      exact List.prefix_rfl
  have attachedExtension := recordSelectedCallResult_success_attachedTypingSourceExtends recordSuccess roots
  have callContains := recordSelectedCallResult_success_containsExpression recordSuccess roots
  have argumentEdge : ∀ argument ∈ [left, right],
      DirectChild (resultState.toTypedSource roots) (.expression fitted.expression.id) (.expression argument.id) := by
    intro argument member
    refine ⟨.expression _, ⟨callContains.1, rfl⟩, ?_⟩
    simp only [nodeChildIds, Node.references, ExpressionForm.references, List.mem_cons]
    exact Or.inr (List.mem_map.mpr ⟨argument.id, List.mem_map.mpr ⟨argument, member, rfl⟩, rfl⟩)
  have entryEdge : ∀ entry ∈ attempt.argumentCoercions,
      DirectChild (resultState.toTypedSource roots) (.expression fitted.expression.id) (.expression entry.expression) := by
    intro entry member
    have idMember : entry.expression ∈ [left, right].map (·.id) := by
      rw [← entryIds]; exact List.mem_map.mpr ⟨entry, member, rfl⟩
    obtain ⟨argument, argumentMember, idEq⟩ := List.mem_map.mp idMember
    rw [← idEq]; exact argumentEdge argument argumentMember
  have argumentPreserved : ∀ argument ∈ [left, right],
      AttachedChildPreserved finalized.substitution (rightState.toTypedSource roots)
        semanticSource finalized.typedSource (evidenceState.toTypedSource roots) argument.id := by
    intro argument member
    have idMember : argument.id ∈ attempt.argumentCoercions.map (·.expression) := by
      rw [entryIds]; exact List.mem_map.mpr ⟨argument, member, rfl⟩
    obtain ⟨entry, entryMember, idEq⟩ := List.mem_map.mp idMember
    rw [← idEq]
    exact (AttachedChildPreserved.of_attachment fitted.state attempt.argumentCoercions roots
      attachedExtension entryIdsUnique entryEdge semanticPreserved finalPreserved rawProper
      childrenRetained resources.graph_closed entry entryMember).monoBefore rightToFitted
  have fittedRequirements := Detail.recordSelectedCallResult_requirements_subset expression callee name
    [left, right] attempt fitted.expression fitted.coercions fitted.state
  rw [recordSuccess] at fittedRequirements
  have attemptRequirements := (Detail.withExpected_requirements_subset fitting).trans fittedRequirements
  have rightRequirements := (Detail.tryFunctionCandidate_requirements_subset candidateSuccess).trans
    (attemptRequirements.trans requirementsSubset)
  have rightPatterns : rightState.integerPatterns ⊆ evidenceState.integerPatterns := by
    have recordedPatterns := Detail.SelectedMetadata.recordSelectedCallResult_integerPatterns_eq
      expression callee name [left, right] attempt fitted.expression fitted.coercions fitted.state
    rw [recordSuccess, Detail.SelectedMetadata.withExpected_integerPatterns_eq fitting,
      Detail.SelectedMetadata.tryFunctionCandidate_integerPatterns_eq candidateSuccess] at recordedPatterns
    rw [← recordedPatterns]
    exact integerPatternsSubset
  have rightLiterals : rightState.integerLiterals ⊆ evidenceState.integerLiterals := by
    have recordedLiterals := Detail.SelectedMetadata.recordSelectedCallResult_integerLiterals_eq
      expression callee name [left, right] attempt fitted.expression fitted.coercions fitted.state
    rw [recordSuccess, Detail.SelectedMetadata.withExpected_integerLiterals_eq fitting,
      Detail.SelectedMetadata.tryFunctionCandidate_integerLiterals_eq candidateSuccess] at recordedLiterals
    rw [← recordedLiterals]
    exact integerLiteralsSubset
  have leftNodes := (Detail.inferExprFuel_occurrenceBoundExtends leftSuccess).nodesBelowNextOccurrence allocatedInvariant.nodesBelow
  have leftToRight := inferExprFuel_success_typingSourceExtends rightSuccess leftNodes roots
  have leftPreserved := (argumentPreserved left (by simp)).monoBefore leftToRight
  have leftTyped := recursive leftSuccess resources interfaces leftExtension signaturesEq ownerEq
    typeParametersEq assumptionsEq signatureFormation functionsCanonical catalog canonical allocatedInvariant actual allocatedOperational
    (by simp) (by simp) leftPreserved.finalized leftPreserved.raw
    ((Detail.inferExprFuel_integerPatterns_subset rightSuccess).trans rightPatterns)
    ((Detail.inferExprFuel_integerLiterals_subset rightSuccess).trans rightLiterals)
    ((Detail.inferExprFuel_requirements_subset rightSuccess).trans rightRequirements)
    leftPreserved.requirements leftPreserved.coercions leftPreserved.operators leftPreserved.children
    (covered.expressionChild resources.graph_closed (childrenRetained (argumentEdge left (by simp))))
    leftPreserved.semantic (actualCovered.directChild (childrenRetained (argumentEdge left (by simp))))
  have leftInvariant := allocatedInvariant.ofExpression signatureFormation functionsCanonical (by simp) leftExtension leftSuccess
  have leftOperational := allocatedOperational.ofExpression leftSuccess leftProperties.1.next_le
  have rightPreserved := argumentPreserved right (by simp)
  have rightTyped := recursive rightSuccess resources interfaces rightExtension signaturesEq ownerEq
    typeParametersEq assumptionsEq signatureFormation functionsCanonical catalog canonical leftInvariant actual leftOperational
    (by simp) (by simp) rightPreserved.finalized rightPreserved.raw rightPatterns rightLiterals rightRequirements
    rightPreserved.requirements rightPreserved.coercions rightPreserved.operators rightPreserved.children
    (covered.expressionChild resources.graph_closed (childrenRetained (argumentEdge right (by simp))))
    rightPreserved.semantic (actualCovered.directChild (childrenRetained (argumentEdge right (by simp))))
  have argumentBases : ArgumentTypingBasesValid (rightState.toTypedSource roots)
      semanticSource semanticContext finalized.substitution [left, right] :=
    .cons (leftTyped.weakenNodeSource leftToRight.nodes_prefix) (.cons rightTyped .nil)
  have argumentSemantic : ExpressionNodesPreservedAt ([left, right].map (·.id))
      (((Detail.attachExpressionCoercions fitted.state attempt.argumentCoercions).toTypedSource roots).applySubstitution finalized.substitution)
      semanticSource := by
    intro id node member contains
    obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp member
    exact ((semanticPreserved.childSubtree (argumentEdge argument argumentMember)).monoBefore attachedExtension).expressionNode
      (by simp) contains
  have argumentFinal : ExpressionNodesPreservedAt ([left, right].map (·.id))
      (((Detail.attachExpressionCoercions fitted.state attempt.argumentCoercions).toTypedSource roots).applySubstitution finalized.substitution)
      finalized.typedSource := by
    intro id node member contains
    obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp member
    exact ((finalPreserved.childSubtree (argumentEdge argument argumentMember)).monoBefore attachedExtension).expressionNode
      (by simp) contains
  have calleeEdge : DirectChild (resultState.toTypedSource roots) (.expression fitted.expression.id)
      (.expression (Detail.attachExpressionCoercions fitted.state attempt.argumentCoercions).allocateExpressionId.1) := by
    refine ⟨.expression _, ⟨callContains.1, rfl⟩, ?_⟩
    simp [nodeChildIds, Node.references, ExpressionForm.references]
  have calleeSemantic : ExpressionNodesPreservedAt
      [(Detail.attachExpressionCoercions fitted.state attempt.argumentCoercions).allocateExpressionId.1]
      ((resultState.toTypedSource roots).applySubstitution finalized.substitution) semanticSource :=
    (semanticPreserved.childSubtree calleeEdge).expressionNode
  have binders := invariant.typeParameterBinders (by simpa [ownerEq, typeParametersEq] using canonical)
  have range := resources.substitutionRangeAdmissible binders invariant.signatures_eq_whole
    invariant.typeParametersEq invariant.declarationEq invariant.residual
  have activeCatalog : SignatureCatalogWellFormed semanticContext.signatures := by
    rw [activeSignaturesEq]; exact catalog
  have finalSubstitutionEq := resources.substitution_eq.symm
  have finalExtension : resources.finalState.inference.substitution.SemanticallyExtends attempt.state.inference.substitution := by
    simpa only [finalSubstitutionEq] using attemptExtension
  have finalRequirements : attempt.state.requirements ⊆ resources.finalState.requirements := by
    rw [resources.requirements_eq]
    exact attemptRequirements.trans requirementsSubset
  have finalFitted : resources.finalState.inference.substitution.SemanticallyExtends fitted.state.inference.substitution := by
    simpa only [finalSubstitutionEq] using fittedExtension
  have fittedRequirementsFinal : fitted.state.requirements ⊆ resources.finalState.requirements := by
    rw [resources.requirements_eq]
    exact fittedRequirements.trans requirementsSubset
  have present : CoercionPrimariesPresent finalized.typedSource fitted.coercions := by
    intro step member
    obtain ⟨node, found, finalStep, site, same⟩ := coercionsRetained callContains step
      (List.mem_append_left _ (List.mem_append_right _ member))
    exact ⟨node, found.1, finalStep, site, same⟩
  have occurs : ∀ requirement ∈ coercionRequirementIds fitted.coercions,
      PrimaryRequirementOccursAt finalized.typedSource (.expression fitted.expression.id) requirement := by
    intro requirement member
    apply retained callContains
    exact List.mem_append_right _ (by simpa only [Detail.coercionRequirements, coercionRequirementIds] using member)
  have trailing := withExpected_success_coercionPathValid_from_interfaces
    (later := resources.finalState) (base := finalizedRequirementContext wholeContext finalized)
    fitting (by simpa only [signaturesEq] using interfaces) present fittedRequirementsFinal
    activeCatalog activeSignaturesEq resources.solve_success resources.solved_context_eq resources.ledger resources.ownership
    invariant.signaturesEq invariant.solvedRequirementsEq invariant.assumptionsMono covered occurs
  simp only [State.resolve, TypeSystem.InferState.apply_resolve_eq_apply finalFitted] at trailing
  simpa only [finalSubstitutionEq] using
    (tryFunctionCandidate_recordSelectedCallResult_typing_from_interfaces
      (solverContext := wholeContext) (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      signatureCanonical candidateSuccess recordSuccess (Detail.withExpected_occurrenceState_eq fitting).1 resultIdEq
      (by simpa only [finalSubstitutionEq] using argumentBases) argumentIdsUnique
      rightProperties.2.1 argumentsBelow schemeBelow boolBelow
      finalExtension finalFitted finalRequirements
      (by
        intro id node member found
        apply argumentSemantic member
        simpa only [finalSubstitutionEq] using found)
      (by
        intro id node member found
        apply calleeSemantic member
        simpa only [finalSubstitutionEq] using found)
      (by
        intro id node member found
        apply argumentFinal member
        simpa only [finalSubstitutionEq] using found)
      retained (by simpa only [signaturesEq] using interfaces) coercionsRetained
      (fun entry member => covered.expressionChild resources.graph_closed (childrenRetained (entryEdge entry member)))
      activeCatalog binders invariant.residual (by simpa only [finalSubstitutionEq] using range)
      signatureMember activeSignaturesEq resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership invariant.signaturesEq invariant.solvedRequirementsEq
      invariant.assumptionsMono covered trailing)

theorem actualInferExprFuelRetainedSoundness_binary {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression leftExpression rightExpression : Syntax.Expr} {operator : Syntax.Located Syntax.BinaryOp} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .binary leftExpression operator rightExpression →
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
  intro wholeContext inferenceContext wholeReturn expression leftExpression rightExpression operator expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained operatorsRetained childrenRetained covered semanticPreserved actualCovered
  generalize allocationEq : initial.allocateExpressionId = pair
  obtain ⟨id, allocated⟩ := pair
  obtain ⟨left, leftState, right, rightState, leftSuccess, rightSuccess, dispatch⟩ :=
    Detail.inferExprFuel_success_binary_facts expressionEq allocationEq success
  cases dispatch with
  | directFunction dispatch lookup operatorSuccess recorded =>
      exact actualInferExprFuelRetainedSoundness_binary_operator recursive
        expressionEq success resources interfaces resultSubstitutionExtension signaturesEq ownerEq typeParametersEq
        assumptionsEq signatureFormation functionsCanonical catalog canonical invariant actual operational
        expectedBelow expectedAdmissible finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
        retained coercionsRetained operatorsRetained childrenRetained covered semanticPreserved actualCovered
        allocationEq leftSuccess rightSuccess operatorSuccess recorded
  | traitMethod dispatch operatorSuccess recorded =>
      exact actualInferExprFuelRetainedSoundness_binary_operator recursive
        expressionEq success resources interfaces resultSubstitutionExtension signaturesEq ownerEq typeParametersEq
        assumptionsEq signatureFormation functionsCanonical catalog canonical invariant actual operational
        expectedBelow expectedAdmissible finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
        retained coercionsRetained operatorsRetained childrenRetained covered semanticPreserved actualCovered
        allocationEq leftSuccess rightSuccess operatorSuccess recorded
  | selectedFunction dispatch lookup selected fitted recorded =>
      exact actualInferExprFuelRetainedSoundness_binary_selected recursive
        expressionEq success resources interfaces resultSubstitutionExtension signaturesEq ownerEq typeParametersEq
        assumptionsEq signatureFormation functionsCanonical catalog canonical invariant actual operational
        expectedBelow expectedAdmissible finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
        retained coercionsRetained operatorsRetained childrenRetained covered semanticPreserved actualCovered
        allocationEq leftSuccess rightSuccess selected fitted recorded
        (Detail.functionsNamed_success_subset_catalog lookup)

end Solcore.SourceSemantics.SourceInferenceSoundness
