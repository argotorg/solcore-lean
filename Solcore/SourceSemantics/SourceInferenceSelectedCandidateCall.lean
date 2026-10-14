import Solcore.SourceSemantics.SourceInferenceSelectedCandidateApplication

/-! The actual selected call retains every attached operand and synthetic
callee node. Only genuine retained coercion sites supply method interfaces. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem tryFunctionCandidate_recordSelectedCallResult_typing_from_interfaces
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {source callee : Syntax.Expr} {name : String}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state recordState later : Frontend.SourceInference.State}
    {signature : ProgramFunctionSignature}
    {attempt : Detail.CandidateAttemptResult}
    {result : InferredExpression}
    {trailingCoercions : List CoercionStep}
    {recorded : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    (canonical : signature.scheme.body = .function
      (TypeSystem.Ty.productMany signature.parameterTypes)
      (TypeSystem.Ty.productMany signature.returnTypes))
    (candidateSuccess : Detail.tryFunctionCandidate inferenceContext arguments
      integerLiteralOrigins call expected state signature = .ok (some attempt))
    (recordSuccess : Detail.recordSelectedCallResult source callee name
      arguments attempt result trailingCoercions recordState = recorded)
    (recordNodesEq : recordState.nodes = attempt.state.nodes)
    (resultIdEq : result.id = attempt.result.id)
    (bases : ArgumentTypingBasesValid (state.toTypedSource roots)
      semanticSource active later.inference.substitution arguments)
    (argumentIdsUnique : (arguments.map (·.id)).Nodup)
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (schemeBodyBelow : signature.scheme.body.VariablesBelow
      state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (candidateSubstitutionExtends :
      later.inference.substitution.SemanticallyExtends
        attempt.state.inference.substitution)
    (recordSubstitutionExtends :
      later.inference.substitution.SemanticallyExtends
        recordState.inference.substitution)
    (candidateRequirementsSubset :
      attempt.state.requirements ⊆ later.requirements)
    (semanticArgumentNodesPreserved : ExpressionNodesPreservedAt
      (arguments.map (·.id))
      ((Detail.attachExpressionCoercions recordState
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      semanticSource)
    (semanticCalleeNodePreserved : ExpressionNodesPreservedAt
      [((Detail.attachExpressionCoercions recordState
          attempt.argumentCoercions).allocateExpressionId.1)]
      ((recorded.2.toTypedSource roots).applySubstitution
        later.inference.substitution)
      semanticSource)
    (evidenceArgumentNodesPreserved : ExpressionNodesPreservedAt
      (arguments.map (·.id))
      ((Detail.attachExpressionCoercions recordState
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      evidenceSource)
    (callRequirementsRetained : ExpressionRequirementsRetainedAt
      (recorded.2.toTypedSource roots) evidenceSource result.id)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces inferenceContext.signatures solved evidenceSource)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (recorded.2.toTypedSource roots) evidenceSource result.id)
    (argumentCovered : ∀ entry ∈ attempt.argumentCoercions,
      TemplateScopeCovered evidenceSource active
        (.expression entry.expression))
    (catalog : SignatureCatalogWellFormed active.signatures)
    (binders : TypeParameterBindersWellFormed active)
    (residual : active.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible active later.inference.substitution)
    (signatureMember : signature ∈ active.signatures.functions)
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
      (.expression result.id))
    (trailingPath : CoercionPathValid active
      (later.inference.substitution.apply attempt.result.type)
      (later.inference.substitution.apply result.type)
      (trailingCoercions.map
        (CoercionStep.applySubstitution later.inference.substitution))) :
    ExpressionTypingBase (recorded.2.toTypedSource roots) semanticSource active
      later.inference.substitution result := by
  let instantiated := signature.scheme.instantiate state.inference.next
  have mappedApplication := tryFunctionCandidate_application_afterSubstitution
    catalog binders residual range signatureMember candidateSuccess
  have rawAdmissible := DeclarationApplicationValid.result_type_admissible catalog binders mappedApplication
  have parameterAdmissible := DeclarationApplicationValid.parameter_types_admissible catalog binders mappedApplication
  have candidateNodesEq : attempt.state.nodes = state.nodes :=
    (Detail.tryFunctionCandidate_some_occurrenceState_eq candidateSuccess).1
  have nodesPrefix :
      (state.toTypedSource roots).nodes <+:
        (recordState.toTypedSource roots).nodes := by
    change state.nodes <+: recordState.nodes
    rw [recordNodesEq, candidateNodesEq]
    exact List.prefix_rfl
  have recordBases : ArgumentTypingBasesValid
      (recordState.toTypedSource roots) semanticSource active
      later.inference.substitution arguments :=
    bases.weakenNodeSource nodesPrefix
  have argumentExpressionIds :
      attempt.argumentCoercions.map (·.expression) =
        arguments.map (·.id) :=
    Detail.tryFunctionCandidate_some_argumentCoercion_expression_ids
      canonical candidateSuccess
  have entryIdsUnique :
      (attempt.argumentCoercions.map (·.expression)).Nodup := by
    rw [argumentExpressionIds]
    exact argumentIdsUnique
  have argumentOccurs : ∀ entry ∈ attempt.argumentCoercions,
      ∀ requirement,
        requirement ∈ coercionRequirementIds entry.coercions →
          PrimaryRequirementOccursAt evidenceSource
            (.expression entry.expression) requirement := by
    intro entry entryMember requirement requirementMember
    have entryIdMember : entry.expression ∈ arguments.map (·.id) := by
      rw [← argumentExpressionIds]
      exact List.mem_map.mpr ⟨entry, entryMember, rfl⟩
    obtain ⟨argument, argumentMember, argumentIdEq⟩ :=
      List.mem_map.mp entryIdMember
    obtain ⟨node, contains⟩ :=
      recordBases.containsExpression_of_mem argumentMember
    have entryContains : ContainsExpression
        (recordState.toTypedSource roots) entry.expression node := by
      rwa [← argumentIdEq]
    have attachedContains := attachExpressionCoercions_containsExpression
      recordState attempt.argumentCoercions entry node roots entryIdsUnique
      entryMember entryContains
    have substitutedContains :=
      FlexibleSubstitution.ContainsExpression.applySubstitution
        later.inference.substitution attachedContains
    have finalContains :=
      evidenceArgumentNodesPreserved entryIdMember substitutedContains
    apply finalContains.primaryRequirementOccursAt
    change requirement ∈
      node.requirements ++ Detail.coercionRequirements entry.coercions
    apply List.mem_append_right
    simpa [Detail.coercionRequirements, coercionRequirementIds] using
      requirementMember
  have argumentPresent : ∀ entry ∈ attempt.argumentCoercions,
      CoercionPrimariesPresent evidenceSource entry.coercions := by
    intro entry entryMember step stepMember
    have entryIdMember : entry.expression ∈ arguments.map (·.id) := by
      rw [← argumentExpressionIds]
      exact List.mem_map.mpr ⟨entry, entryMember, rfl⟩
    obtain ⟨argument, argumentMember, argumentIdEq⟩ := List.mem_map.mp entryIdMember
    obtain ⟨node, contains⟩ := recordBases.containsExpression_of_mem argumentMember
    have entryContains : ContainsExpression (recordState.toTypedSource roots) entry.expression node := by
      rwa [← argumentIdEq]
    have attached := attachExpressionCoercions_containsExpression
      recordState attempt.argumentCoercions entry node roots entryIdsUnique entryMember entryContains
    have finalFound := evidenceArgumentNodesPreserved entryIdMember
      (FlexibleSubstitution.ContainsExpression.applySubstitution later.inference.substitution attached)
    refine ⟨_, finalFound.1, step.applySubstitution later.inference.substitution, ?_, rfl⟩
    apply List.mem_append_left
    change step.applySubstitution later.inference.substitution ∈
      (node.coercions ++ entry.coercions).map (CoercionStep.applySubstitution later.inference.substitution)
    exact List.mem_map.mpr ⟨step, List.mem_append_right _ stepMember, rfl⟩
  have argumentCoercions : ArgumentCoercionsValid active
      later.inference.substitution arguments
      (signature.parameterTypes.map instantiated.parameterSubstitution.apply)
      attempt.argumentCoercions := by
    simpa only [instantiated] using
      tryFunctionCandidate_some_argumentCoercionsValid_from_interfaces
        canonical candidateSuccess ready argumentsBelow schemeBodyBelow
        expectedBelow candidateSubstitutionExtends
        candidateRequirementsSubset interfaces argumentPresent
        (by intro parameter member; exact parameterAdmissible _ (List.mem_map.mpr ⟨parameter, member, rfl⟩))
        catalog signaturesEq
        solveSuccess solvedEq ledger ownership activeSignaturesEq
        activeRequirementsEq assumptionsMono argumentCovered argumentOccurs
  have selectedCovered : TemplateScopeCovered evidenceSource active
      (.expression attempt.result.id) := by
    simpa only [← resultIdEq] using callCovered
  have selectedOccurs : ∀ requirement,
      requirement ∈ Detail.coercionRequirements attempt.callCoercions ++
          attempt.signatureRequirements →
        PrimaryRequirementOccursAt evidenceSource
          (.expression attempt.result.id) requirement := by
    intro requirement member
    have callContains :=
      recordSelectedCallResult_success_containsExpression recordSuccess roots
    have occurs := callRequirementsRetained callContains
      (List.mem_append_left
        (Detail.coercionRequirements trailingCoercions) member)
    simpa only [← resultIdEq] using occurs
  have instantiationPredicatesEq :
      attempt.instantiation.predicates = instantiated.predicates := by
    rw [Detail.tryFunctionCandidate_some_instantiation candidateSuccess]
    rfl
  have callRequirements : DirectCallRequirementsValid active
      (later.inference.substitution.apply
        (instantiated.parameterSubstitution.apply
          (TypeSystem.Ty.productMany signature.returnTypes)))
      (later.inference.substitution.apply attempt.result.type)
      (instantiated.predicates.map
        (TypedTraitResolution.applySubstitution
          later.inference.substitution))
      (Detail.coercionRequirements attempt.callCoercions ++
        attempt.signatureRequirements)
      (attempt.callCoercions.map
        (CoercionStep.applySubstitution
          later.inference.substitution)) := by
    rw [← instantiationPredicatesEq]
    simpa only [instantiated] using
      tryFunctionCandidate_some_directCallRequirementsValid_from_interfaces
        canonical candidateSuccess ready argumentsBelow schemeBodyBelow
        expectedBelow candidateSubstitutionExtends
        candidateRequirementsSubset interfaces
        (by intro step member
            exact coercionsRetained.present
              (recordSelectedCallResult_success_containsExpression recordSuccess roots) step
              (List.mem_append_left _ (List.mem_append_left _ member))) catalog signaturesEq solveSuccess solvedEq ledger
        ownership activeSignaturesEq activeRequirementsEq assumptionsMono
        selectedCovered selectedOccurs
  let attachedState := Detail.attachExpressionCoercions recordState
    attempt.argumentCoercions
  let allocation := attachedState.allocateExpressionId
  let calleeNode : ExpressionNode := {
    id := allocation.1
    span := callee.span
    type := allocation.2.resolve attempt.instantiation.type
    form := .reference name (.declaration attempt.instantiation)
  }
  let callNode : ExpressionNode := {
    id := result.id
    span := source.span
    type := result.type
    form := .call allocation.1 (arguments.map (·.id))
      (.declaration attempt.instantiation)
    requirements :=
      Detail.coercionRequirements attempt.callCoercions ++
        attempt.signatureRequirements ++
        Detail.coercionRequirements trailingCoercions
    coercions := attempt.callCoercions ++ trailingCoercions
  }
  have rawContains : ContainsExpression (recorded.2.toTypedSource roots)
      result.id callNode := by
    simpa only [attachedState, allocation, callNode] using
      recordSelectedCallResult_success_containsExpression recordSuccess roots
  have argumentsType : ExpressionsHaveTypes semanticSource active
      (arguments.map (·.id))
      ((signature.parameterTypes.map
        instantiated.parameterSubstitution.apply).map
          later.inference.substitution.apply) :=
    argumentTypingBasesValid_attachExpressionCoercions_expressionsHaveTypes
      recordBases argumentCoercions argumentIdsUnique
        semanticArgumentNodesPreserved
  have rawCalleeContains : ContainsExpression
      (recorded.2.toTypedSource roots) allocation.1 calleeNode := by
    have nodes := Detail.recordSelectedCallResult_success_nodes recordSuccess
    refine ⟨?_, rfl⟩
    change .expression calleeNode ∈ recorded.2.nodes
    rw [nodes.2]
    simp [attachedState, allocation, calleeNode]
  have substitutedCalleeContains : ContainsExpression
      ((recorded.2.toTypedSource roots).applySubstitution
        later.inference.substitution)
      allocation.1
      (calleeNode.applySubstitution later.inference.substitution) :=
    FlexibleSubstitution.ContainsExpression.applySubstitution
      later.inference.substitution rawCalleeContains
  have finalCalleeContains : ContainsExpression semanticSource allocation.1
      (calleeNode.applySubstitution later.inference.substitution) :=
    semanticCalleeNodePreserved (by simp [attachedState, allocation])
      substitutedCalleeContains
  have mappedInstantiationValid : SourceSemantics.DeclarationInstantiation.Admissible active
      (attempt.instantiation.applySubstitution later.inference.substitution) := by
    cases mappedApplication with
    | intro _ valid _ _ _ _ _ => exact valid
  have allocationInferenceEq : allocation.2.inference =
      recordState.inference := by
    calc
      allocation.2.inference = attachedState.inference := by rfl
      _ = recordState.inference :=
        Detail.attachExpressionCoercions_inference_eq recordState
          attempt.argumentCoercions
  have allocationExtends :
      later.inference.substitution.SemanticallyExtends
        allocation.2.inference.substitution := by
    rw [allocationInferenceEq]
    exact recordSubstitutionExtends
  have normalizedCalleeType :
      later.inference.substitution.apply
          (allocation.2.resolve attempt.instantiation.type) =
        later.inference.substitution.apply attempt.instantiation.type :=
    TypeSystem.InferState.apply_resolve_eq_apply allocationExtends _
  have calleeValid : DirectDeclarationCalleeValid active semanticSource
      allocation.1
      (attempt.instantiation.applySubstitution
        later.inference.substitution) := by
    refine DirectDeclarationCalleeValid.intro (name := name)
      finalCalleeContains ?_ mappedInstantiationValid ?_ ?_ ?_
    · rfl
    · simpa [calleeNode, ExpressionNode.applySubstitution,
        DeclarationInstantiation.applySubstitution] using normalizedCalleeType
    · rfl
    · rfl
  have formType : ExpressionFormHasRawType semanticSource active
      (callNode.applySubstitution later.inference.substitution).form
      (later.inference.substitution.apply
        (instantiated.parameterSubstitution.apply
          (TypeSystem.Ty.productMany signature.returnTypes)))
      (.directCall
        (instantiated.predicates.map
          (TypedTraitResolution.applySubstitution
            later.inference.substitution))) := by
    simpa [callNode, instantiated, ExpressionNode.applySubstitution,
      ExpressionForm.applySubstitution, CallResolution.applySubstitution] using
        (ExpressionFormHasRawType.directCall calleeValid mappedApplication
          argumentsType)
  refine .intro rawContains (by rfl) formType rawAdmissible ?_
  have requirements :=
    (ExpressionRequirementPlan.Valid.directCall callRequirements).appendOutput
      trailingPath
  rw [FlexibleSubstitution.coercionRequirementIds_applySubstitution]
    at requirements
  simpa [callNode, ExpressionNode.applySubstitution, List.map_append,
    Detail.coercionRequirements, coercionRequirementIds,
    List.append_assoc] using requirements


end Solcore.SourceSemantics.SourceInferenceSoundness
