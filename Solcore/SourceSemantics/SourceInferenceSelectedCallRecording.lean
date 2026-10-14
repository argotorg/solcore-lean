import Solcore.SourceSemantics.SourceInferenceSelectedCandidateCall

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem selectFunctionCandidateFrom_recordSelectedCall_typing_from_interfaces
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {source callee : Syntax.Expr} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state later : Frontend.SourceInference.State}
    {attempt : Detail.CandidateAttemptResult}
    {result : InferredExpression}
    {resultState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    (selectionSuccess : Detail.selectFunctionCandidateFrom inferenceContext
      name candidates arguments integerLiteralOrigins call expected state =
        .ok attempt)
    (recordEq : Detail.recordSelectedCall source callee name arguments attempt =
      (result, resultState))
    (candidatesSubset : candidates ⊆
      inferenceContext.signatures.functions)
    (bases : ArgumentTypingBasesValid (state.toTypedSource roots)
      semanticSource active later.inference.substitution arguments)
    (argumentIdsUnique : (arguments.map (·.id)).Nodup)
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ later.requirements)
    (semanticArgumentNodesPreserved : ExpressionNodesPreservedAt
      (arguments.map (·.id))
      ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      semanticSource)
    (semanticCalleeNodePreserved : ExpressionNodesPreservedAt
      [((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions).allocateExpressionId.1)]
      ((resultState.toTypedSource roots).applySubstitution
        later.inference.substitution)
      semanticSource)
    (evidenceArgumentNodesPreserved : ExpressionNodesPreservedAt
      (arguments.map (·.id))
      ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      evidenceSource)
    (callRequirementsRetained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) evidenceSource result.id)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces inferenceContext.signatures solved evidenceSource)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) evidenceSource result.id)
    (argumentCovered : ∀ entry ∈ attempt.argumentCoercions,
      TemplateScopeCovered evidenceSource active
        (.expression entry.expression))
    (catalog : SignatureCatalogWellFormed active.signatures)
    (binders : TypeParameterBindersWellFormed active)
    (residual : active.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible active later.inference.substitution)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base evidenceSource)
    (ownership : RequirementOwnership base evidenceSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (callCovered : TemplateScopeCovered evidenceSource active
      (.expression result.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource active
      later.inference.substitution result := by
  obtain ⟨signature, _, signatureMember, canonical, schemeBodyBelow,
      candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_semanticCandidate signatureFormation
      functionsCanonical signaturesEq candidatesSubset selectionSuccess
  have candidateProperties :=
    Detail.tryFunctionCandidate_some_inferenceProperties ready argumentsBelow
      schemeBodyBelow expectedBelow candidateSuccess
  have recordProperties := Detail.recordSelectedCall_inferenceProperties
    source callee name arguments attempt candidateProperties.2.1
      candidateProperties.2.2
  rw [recordEq] at recordProperties
  have laterExtendsAttempt :
      later.inference.substitution.SemanticallyExtends
        attempt.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
      recordProperties.1.substitution_extends
  have attemptRequirementsAtResult :=
    Detail.recordSelectedCall_requirements_subset source callee name arguments
      attempt
  rw [recordEq] at attemptRequirementsAtResult
  have attemptRequirementsAtLater :
      attempt.state.requirements ⊆ later.requirements :=
    List.Subset.trans attemptRequirementsAtResult requirementsSubset
  have recordSuccess : Detail.recordSelectedCallResult source callee name
      arguments attempt attempt.result [] attempt.state =
        (result, resultState) := by
    simpa only [Detail.recordSelectedCall] using recordEq
  have resultEq : result = attempt.result :=
    (Detail.recordSelectedCallResult_success_nodes recordSuccess).1
  subst result
  exact
    tryFunctionCandidate_recordSelectedCallResult_typing_from_interfaces
      canonical candidateSuccess recordSuccess rfl rfl bases
      argumentIdsUnique ready argumentsBelow schemeBodyBelow expectedBelow
      laterExtendsAttempt laterExtendsAttempt attemptRequirementsAtLater
      semanticArgumentNodesPreserved semanticCalleeNodePreserved
      evidenceArgumentNodesPreserved callRequirementsRetained interfaces coercionsRetained argumentCovered
      catalog binders residual range signatureMember signaturesEq
      solveSuccess solvedEq ledger
      ownership activeSignaturesEq activeRequirementsEq assumptionsMono
      callCovered (.nil _)

end Solcore.SourceSemantics.SourceInferenceSoundness
