import Solcore.SourceSemantics.SourceInferenceSelectedRetainedExpressionList
import Solcore.SourceSemantics.SourceInferenceSelectedCandidateCall
import Solcore.SourceSemantics.SourceInferenceSelectedOperatorMetadata

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualSelectedCall_typing {fuel : Nat}
    (recursive : ∀ smaller, smaller < fuel → ActualInferExprFuelRetainedSoundness smaller) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression callee : Syntax.Expr} {expected : Option Ty}
    {argumentSources : List Syntax.Expr} {arguments : List InferredExpression}
    {name : String} {candidates : List ProgramFunctionSignature}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {attempt : Detail.CandidateAttemptResult}
    {initial argumentState resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    Detail.inferExprsFuel fuel inferenceContext argumentSources initial = .ok (arguments, argumentState) →
    Detail.selectFunctionCandidateFrom inferenceContext name candidates arguments integerLiteralOrigins
      call expected argumentState = .ok attempt →
    Detail.recordSelectedCall expression callee name arguments attempt = (inferred, resultState) →
    candidates ⊆ inferenceContext.signatures.functions →
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
  intro wholeContext inferenceContext wholeReturn expression callee expected argumentSources arguments
    name candidates integerLiteralOrigins call attempt initial argumentState resultState evidenceState
    inferred roots finalized semanticSource frames semanticContext argumentsSuccess selectionSuccess
    recording candidatesSubset resources interfaces resultSubstitutionExtension signaturesEq ownerEq
    typeParametersEq assumptionsEq signatureFormation functionsCanonical catalog canonical invariant
    actual operational expectedBelow expectedAdmissible finalPreserved rawProper integerPatternsSubset
    integerLiteralsSubset requirementsSubset retained coercionsRetained _operatorsRetained childrenRetained covered
    semanticPreserved actualCovered
  have recordSuccess : Detail.recordSelectedCallResult expression callee name arguments attempt
      attempt.result [] attempt.state = (inferred, resultState) := by
    simpa only [Detail.recordSelectedCall] using recording
  have inferredEq : inferred = attempt.result := (Detail.recordSelectedCallResult_success_nodes recordSuccess).1
  subst inferred
  have activeSignaturesEq := invariant.signatures_eq_whole.trans signaturesEq.symm
  obtain ⟨signature, _, signatureMember, signatureCanonical, schemeBelow, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_semanticCandidate signatureFormation functionsCanonical
      activeSignaturesEq candidatesSubset selectionSuccess
  have argumentProperties := Detail.inferExprsFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical argumentsSuccess
  have expectedAtArguments : ∀ type ∈ expected, type.VariablesBelow argumentState.inference.next :=
    fun type member => (expectedBelow type member).weaken argumentProperties.1.next_le
  have candidateProperties := Detail.tryFunctionCandidate_some_inferenceProperties
    argumentProperties.2.1 argumentProperties.2.2 schemeBelow expectedAtArguments candidateSuccess
  have recordProperties := Detail.recordSelectedCall_inferenceProperties expression callee name arguments
    attempt candidateProperties.2.1 candidateProperties.2.2
  rw [recording] at recordProperties
  have attemptExtension := resultSubstitutionExtension.trans recordProperties.1.substitution_extends
  have argumentExtension := attemptExtension.trans candidateProperties.1.substitution_extends
  have argumentIdsUnique := Detail.inferExprsFuel_success_ids_nodup argumentsSuccess
  have entryIds : attempt.argumentCoercions.map (·.expression) = arguments.map (·.id) :=
    Detail.tryFunctionCandidate_some_argumentCoercion_expression_ids signatureCanonical candidateSuccess
  have entryIdsUnique : (attempt.argumentCoercions.map (·.expression)).Nodup := by
    rw [entryIds]; exact argumentIdsUnique
  have argumentToAttempt : TypingSourceExtends (argumentState.toTypedSource roots)
      (attempt.state.toTypedSource roots) := by
    refine ⟨?_, ?_⟩
    · exact congrArg State.Header.owner (Detail.SelectedMetadata.tryFunctionCandidate_some_state_header candidateSuccess)
    · change argumentState.nodes <+: attempt.state.nodes
      rw [(Detail.tryFunctionCandidate_some_occurrenceState_eq candidateSuccess).1]
      exact List.prefix_rfl
  have attachedExtension := recordSelectedCallResult_success_attachedTypingSourceExtends recordSuccess roots
  have callContains := recordSelectedCallResult_success_containsExpression recordSuccess roots
  have argumentEdge : ∀ argument ∈ arguments,
      DirectChild (resultState.toTypedSource roots) (.expression attempt.result.id) (.expression argument.id) := by
    intro argument member
    refine ⟨.expression _, ⟨callContains.1, rfl⟩, ?_⟩
    simp only [nodeChildIds, Node.references, ExpressionForm.references, List.mem_cons]
    exact Or.inr (List.mem_map.mpr ⟨argument.id, List.mem_map.mpr ⟨argument, member, rfl⟩, rfl⟩)
  have entryEdge : ∀ entry ∈ attempt.argumentCoercions,
      DirectChild (resultState.toTypedSource roots) (.expression attempt.result.id) (.expression entry.expression) := by
    intro entry member
    have idMember : entry.expression ∈ arguments.map (·.id) := by
      rw [← entryIds]; exact List.mem_map.mpr ⟨entry, member, rfl⟩
    obtain ⟨argument, argumentMember, idEq⟩ := List.mem_map.mp idMember
    rw [← idEq]; exact argumentEdge argument argumentMember
  have argumentPreserved : ∀ argument ∈ arguments,
      AttachedChildPreserved finalized.substitution (argumentState.toTypedSource roots)
        semanticSource finalized.typedSource (evidenceState.toTypedSource roots) argument.id := by
    intro argument member
    have idMember : argument.id ∈ attempt.argumentCoercions.map (·.expression) := by
      rw [entryIds]; exact List.mem_map.mpr ⟨argument, member, rfl⟩
    obtain ⟨entry, entryMember, idEq⟩ := List.mem_map.mp idMember
    rw [← idEq]
    exact (AttachedChildPreserved.of_attachment attempt.state attempt.argumentCoercions roots
      attachedExtension entryIdsUnique entryEdge semanticPreserved finalPreserved rawProper
      childrenRetained resources.graph_closed entry entryMember).monoBefore argumentToAttempt
  have attemptRequirements := Detail.recordSelectedCall_requirements_subset expression callee name arguments attempt
  rw [recording] at attemptRequirements
  have argumentRequirements := (Detail.tryFunctionCandidate_requirements_subset candidateSuccess).trans
    (attemptRequirements.trans requirementsSubset)
  have argumentPatterns : argumentState.integerPatterns ⊆ evidenceState.integerPatterns := by
    have recordedPatterns := Detail.SelectedMetadata.recordSelectedCallResult_integerPatterns_eq
      expression callee name arguments attempt attempt.result [] attempt.state
    rw [recordSuccess, Detail.SelectedMetadata.tryFunctionCandidate_integerPatterns_eq candidateSuccess] at recordedPatterns
    rw [← recordedPatterns]
    exact integerPatternsSubset
  have argumentLiterals : argumentState.integerLiterals ⊆ evidenceState.integerLiterals := by
    have recordedLiterals := Detail.SelectedMetadata.recordSelectedCallResult_integerLiterals_eq
      expression callee name arguments attempt attempt.result [] attempt.state
    rw [recordSuccess, Detail.SelectedMetadata.tryFunctionCandidate_integerLiterals_eq candidateSuccess] at recordedLiterals
    rw [← recordedLiterals]
    exact integerLiteralsSubset
  have argumentBases := actualInferExprsFuelRetainedBases fuel recursive argumentsSuccess resources interfaces
    argumentExtension signaturesEq ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational argumentPreserved
    argumentPatterns argumentLiterals argumentRequirements
    (fun argument member => covered.expressionChild resources.graph_closed (childrenRetained (argumentEdge argument member)))
    (fun argument member => actualCovered.directChild (childrenRetained (argumentEdge argument member)))
  have argumentSemantic : ExpressionNodesPreservedAt (arguments.map (·.id))
      (((Detail.attachExpressionCoercions attempt.state attempt.argumentCoercions).toTypedSource roots).applySubstitution finalized.substitution)
      semanticSource := by
    intro id node member contains
    obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp member
    exact ((semanticPreserved.childSubtree (argumentEdge argument argumentMember)).monoBefore attachedExtension).expressionNode
      (by simp) contains
  have argumentFinal : ExpressionNodesPreservedAt (arguments.map (·.id))
      (((Detail.attachExpressionCoercions attempt.state attempt.argumentCoercions).toTypedSource roots).applySubstitution finalized.substitution)
      finalized.typedSource := by
    intro id node member contains
    obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp member
    exact ((finalPreserved.childSubtree (argumentEdge argument argumentMember)).monoBefore attachedExtension).expressionNode
      (by simp) contains
  have calleeEdge : DirectChild (resultState.toTypedSource roots) (.expression attempt.result.id)
      (.expression (Detail.attachExpressionCoercions attempt.state attempt.argumentCoercions).allocateExpressionId.1) := by
    refine ⟨.expression _, ⟨callContains.1, rfl⟩, ?_⟩
    simp [nodeChildIds, Node.references, ExpressionForm.references]
  have calleeSemantic : ExpressionNodesPreservedAt
      [(Detail.attachExpressionCoercions attempt.state attempt.argumentCoercions).allocateExpressionId.1]
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
  simpa only [finalSubstitutionEq] using
    (tryFunctionCandidate_recordSelectedCallResult_typing_from_interfaces
      (solverContext := wholeContext) (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      signatureCanonical candidateSuccess recordSuccess rfl rfl
      (by simpa only [finalSubstitutionEq] using argumentBases) argumentIdsUnique
      argumentProperties.2.1 argumentProperties.2.2 schemeBelow expectedAtArguments
      finalExtension finalExtension finalRequirements
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
      invariant.assumptionsMono covered (.nil _))

end Solcore.SourceSemantics.SourceInferenceSoundness
