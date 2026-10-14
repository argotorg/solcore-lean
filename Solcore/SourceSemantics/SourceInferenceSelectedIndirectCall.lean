import Solcore.SourceSemantics.SourceInferenceSelectedIndirectFitting
import Solcore.SourceSemantics.SourceInferenceSelectedExpressionList
import Solcore.SourceSemantics.SourceInferenceSelectedExpressionListState
import Solcore.SourceSemantics.SourceInferenceSelectedOperatorMetadata

/-! The actual indirect-call trace preserves earlier arguments while inferring
its callee, then records both coercion paths on the call. Each child is typed
from its own retained subtree and the actual scope after argument inference. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

private def indirectMetadata (state : State) :=
  (state.owner, state.integerPatterns, state.integerLiterals)

private theorem unify_indirectMetadata {state next : State} {left right : Ty}
    (success : Detail.unify state left right = .ok next) :
    indirectMetadata next = indirectMetadata state := by
  unfold Detail.unify at success
  cases unified : state.inference.unify left right <;>
    simp [Detail.liftUnification, unified, bind, Except.bind] at success
  cases success
  rfl

private theorem withExpected_indirectMetadata
    {context : Frontend.SourceInference.Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : Detail.ExpectationResult}
    (success : Detail.withExpected context state actual expected = .ok result) :
    indirectMetadata result.state = indirectMetadata state := by
  apply Prod.ext
  · exact congrArg State.Header.owner (Detail.SelectedMetadata.withExpected_state_header success)
  · exact Prod.ext (Detail.SelectedMetadata.withExpected_integerPatterns_eq success)
      (Detail.SelectedMetadata.withExpected_integerLiterals_eq success)

theorem applyFunctionType_metadata
    {context : Frontend.SourceInference.Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : Detail.IndirectApplicationResult}
    (success : Detail.applyFunctionType context call calleeType arguments expected state = .ok result) :
    result.state.owner = state.owner ∧ result.state.integerPatterns = state.integerPatterns ∧
      result.state.integerLiterals = state.integerLiterals := by
  have metadata : indirectMetadata result.state = indirectMetadata state := by
    rcases Detail.applyFunctionType_success_facts success with known | fresh
    · obtain ⟨parameter, resultType, fittedArgument, fittedResult, _, argumentSuccess, outputSuccess, rfl⟩ := known
      exact (withExpected_indirectMetadata outputSuccess).trans (withExpected_indirectMetadata argumentSuccess)
    · obtain ⟨resultType, freshState, unifiedState, fittedResult, _, freshEq, unifySuccess, outputSuccess, rfl⟩ := fresh
      have freshMetadata : indirectMetadata freshState = indirectMetadata state := by
        have stateEq : state.fresh.2 = freshState := congrArg Prod.snd freshEq
        rw [← stateEq]
        rfl
      exact (withExpected_indirectMetadata outputSuccess).trans ((unify_indirectMetadata unifySuccess).trans freshMetadata)
  exact ⟨congrArg Prod.fst metadata, congrArg (fun row => row.2.1) metadata,
    congrArg (fun row => row.2.2) metadata⟩

theorem actualIndirectCall_typing {fuel : Nat}
    (recursive : ∀ smaller, smaller < fuel + 1 → ActualInferExprFuelRetainedSoundness smaller) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression calleeSource : Syntax.Expr} {expected : Option Ty}
    {argumentSources : List Syntax.Expr} {arguments : List InferredExpression}
    {callee : InferredExpression} {call : ExpressionId}
    {application : Detail.IndirectApplicationResult}
    {initial argumentState calleeState resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    Detail.inferExprsFuel fuel inferenceContext argumentSources initial = .ok (arguments, argumentState) →
    Detail.inferExprFuel fuel inferenceContext calleeSource none argumentState = .ok (callee, calleeState) →
    Detail.applyFunctionType inferenceContext call callee.type arguments expected calleeState = .ok application →
    Detail.recordIndirectCall expression callee arguments application = (inferred, resultState) →
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
  intro wholeContext inferenceContext wholeReturn expression calleeSource expected argumentSources arguments
    callee call application initial argumentState calleeState resultState evidenceState
    inferred roots finalized semanticSource frames semanticContext argumentsSuccess calleeSuccess applicationSuccess
    recording resources interfaces resultSubstitutionExtension signaturesEq ownerEq
    typeParametersEq assumptionsEq signatureFormation functionsCanonical catalog canonical invariant
    actual operational expectedBelow expectedAdmissible finalPreserved rawProper integerPatternsSubset
    integerLiteralsSubset requirementsSubset retained coercionsRetained _operatorsRetained childrenRetained covered
    semanticPreserved actualCovered
  have inferredEq : inferred = application.result := by
    have same := congrArg Prod.fst recording
    simpa only [Detail.recordIndirectCall_fst] using same.symm
  subst inferred
  have argumentProperties := Detail.inferExprsFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical argumentsSuccess
  have calleeProperties := Detail.inferExprFuel_inferenceProperties argumentProperties.2.1
    signatureFormation functionsCanonical (by simp) calleeSuccess
  have argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow calleeState.inference.next :=
    fun argument member => (argumentProperties.2.2 argument member).weaken calleeProperties.1.next_le
  have expectedAtCallee : ∀ type ∈ expected, type.VariablesBelow calleeState.inference.next :=
    fun type member => (expectedBelow type member).weaken (argumentProperties.1.trans calleeProperties.1).next_le
  have applicationProperties := Detail.applyFunctionType_inferenceProperties
    calleeProperties.2.1 calleeProperties.2.2 argumentsBelow expectedAtCallee applicationSuccess
  have recordProperties := Detail.recordIndirectCall_inferenceProperties expression callee arguments application
    applicationProperties.2.1 applicationProperties.2.2
  rw [recording] at recordProperties
  have applicationExtension := resultSubstitutionExtension.trans recordProperties.1.substitution_extends
  have calleeExtension := applicationExtension.trans applicationProperties.1.substitution_extends
  have argumentExtension := calleeExtension.trans calleeProperties.1.substitution_extends
  have argumentInvariant := invariant.ofExpressions signatureFormation functionsCanonical argumentExtension argumentsSuccess
  have argumentOperational := operational.ofExpressions argumentsSuccess argumentProperties.1.next_le
  have argumentToCallee := inferExprFuel_success_typingSourceExtends calleeSuccess argumentInvariant.nodesBelow roots
  have metadata := applyFunctionType_metadata applicationSuccess
  have calleeToApplication : TypingSourceExtends (calleeState.toTypedSource roots)
      (application.state.toTypedSource roots) := by
    refine ⟨metadata.1, ?_⟩
    change calleeState.nodes <+: application.state.nodes
    rw [(Detail.applyFunctionType_occurrenceState_eq applicationSuccess).1]
    exact List.prefix_rfl
  have applicationToParent : TypingSourceExtends (application.state.toTypedSource roots)
      (resultState.toTypedSource roots) := by
    have stateEq : (Detail.recordIndirectCall expression callee arguments application).2 = resultState := congrArg Prod.snd recording
    rw [← stateEq]
    refine ⟨rfl, ?_⟩
    change application.state.nodes <+: application.state.nodes ++ [_]
    exact List.prefix_append _ _
  have calleeToParent := calleeToApplication.trans applicationToParent
  have argumentToParent := argumentToCallee.trans calleeToParent
  let callMetadata : IndirectCallResolution := {
    argumentCount := arguments.length
    argumentTypeBeforeCoercion := Ty.productMany (arguments.map (·.type))
    argumentTypeAfterCoercion := application.argumentCoercions.foldl
      (fun _ step => step.target) (Ty.productMany (arguments.map (·.type)))
    argumentCoercions := application.argumentCoercions
  }
  let callNode : ExpressionNode := {
    id := application.result.id
    span := expression.span
    type := application.result.type
    form := .call callee.id (arguments.map (·.id)) (.indirect callMetadata)
    requirements := Detail.coercionRequirements application.argumentCoercions ++
      Detail.coercionRequirements application.callCoercions
    coercions := application.callCoercions
  }
  have callContains : ContainsExpression (resultState.toTypedSource roots) application.result.id callNode := by
    have stateEq : (Detail.recordIndirectCall expression callee arguments application).2 = resultState := congrArg Prod.snd recording
    rw [← stateEq]
    exact recordExpression_containsExpression expression application.result
      (.call callee.id (arguments.map (·.id)) (.indirect callMetadata))
      (Detail.coercionRequirements application.argumentCoercions ++ Detail.coercionRequirements application.callCoercions)
      application.callCoercions application.state roots
  have calleeEdge : DirectChild (resultState.toTypedSource roots) (.expression application.result.id) (.expression callee.id) := by
    refine ⟨.expression callNode, ⟨callContains.1, rfl⟩, ?_⟩
    simp [callNode, nodeChildIds, Node.references, ExpressionForm.references]
  have argumentEdge : ∀ argument ∈ arguments,
      DirectChild (resultState.toTypedSource roots) (.expression application.result.id) (.expression argument.id) := by
    intro argument member
    refine ⟨.expression callNode, ⟨callContains.1, rfl⟩, ?_⟩
    simp only [callNode, nodeChildIds, Node.references, ExpressionForm.references, List.mem_cons]
    exact Or.inr (List.mem_map.mpr ⟨argument.id, List.mem_map.mpr ⟨argument, member, rfl⟩, rfl⟩)
  have parentPatterns : resultState.integerPatterns = application.state.integerPatterns := by
    have stateEq : (Detail.recordIndirectCall expression callee arguments application).2 = resultState := congrArg Prod.snd recording
    rw [← stateEq]
    rfl
  have parentLiterals : resultState.integerLiterals = application.state.integerLiterals := by
    have stateEq : (Detail.recordIndirectCall expression callee arguments application).2 = resultState := congrArg Prod.snd recording
    rw [← stateEq]
    rfl
  have calleePatterns : calleeState.integerPatterns ⊆ evidenceState.integerPatterns := by
    rw [← metadata.2.1, ← parentPatterns]
    exact integerPatternsSubset
  have calleeLiterals : calleeState.integerLiterals ⊆ evidenceState.integerLiterals := by
    rw [← metadata.2.2, ← parentLiterals]
    exact integerLiteralsSubset
  have calleeRequirements : calleeState.requirements ⊆ evidenceState.requirements := by
    apply List.Subset.trans (Detail.applyFunctionType_requirements_subset applicationSuccess)
    have recorded := Detail.recordIndirectCall_requirements_subset expression callee arguments application
    rw [recording] at recorded
    exact recorded.trans requirementsSubset
  have argumentsTyped := actualInferExprsFuelFinalSubtreeSoundness fuel
    (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self fuel)))
    argumentsSuccess resources interfaces argumentExtension signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical invariant actual operational
    (fun argument member => (semanticPreserved.childSubtree (argumentEdge argument member)).monoBefore argumentToParent)
    (fun argument member => (finalPreserved.childSubtree (argumentEdge argument member)).monoBefore argumentToParent)
    (fun argument member => ((rawProper.childSubtree (argumentEdge argument member)).monoBefore argumentToParent).proper)
    ((Detail.inferExprFuel_integerPatterns_subset calleeSuccess).trans calleePatterns)
    ((Detail.inferExprFuel_integerLiterals_subset calleeSuccess).trans calleeLiterals)
    ((Detail.inferExprFuel_requirements_subset calleeSuccess).trans calleeRequirements)
    (fun argument member => covered.expressionChild resources.graph_closed (childrenRetained (argumentEdge argument member)))
    (fun argument member => actualCovered.directChild (childrenRetained (argumentEdge argument member)))
  have calleeTyped := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness
    (recursive fuel (Nat.lt_succ_self fuel)) calleeSuccess resources interfaces calleeExtension
    signaturesEq ownerEq typeParametersEq assumptionsEq signatureFormation functionsCanonical catalog canonical
    argumentInvariant actual argumentOperational (by simp) (by simp)
    ((semanticPreserved.childSubtree calleeEdge).monoBefore calleeToParent)
    ((finalPreserved.childSubtree calleeEdge).monoBefore calleeToParent)
    ((rawProper.childSubtree calleeEdge).monoBefore calleeToParent).proper
    calleePatterns calleeLiterals calleeRequirements
    (covered.expressionChild resources.graph_closed (childrenRetained calleeEdge))
    (actualCovered.directChild (childrenRetained calleeEdge))
  have activeSignaturesEq := invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed semanticContext.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  have finalSubstitutionEq := resources.substitution_eq.symm
  have finalRequirements : resultState.requirements ⊆ resources.finalState.requirements := by
    rw [resources.requirements_eq]
    exact requirementsSubset
  simpa only [finalSubstitutionEq] using
    (applyFunctionType_recordIndirectCall_typing_from_interfaces
      (solverContext := wholeContext) (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      applicationSuccess recording calleeProperties.2.1 calleeProperties.2.2 argumentsBelow expectedAtCallee
      (by simpa only [finalSubstitutionEq] using resultSubstitutionExtension)
      finalRequirements retained coercionsRetained (by simpa only [signaturesEq] using interfaces)
      (by simpa only [finalSubstitutionEq] using argumentsTyped)
      (by simpa only [finalSubstitutionEq] using calleeTyped)
      activeCatalog activeSignaturesEq resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership invariant.signaturesEq invariant.solvedRequirementsEq
      invariant.assumptionsMono covered)

end Solcore.SourceSemantics.SourceInferenceSoundness
