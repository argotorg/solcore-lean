import Solcore.SourceSemantics.SourceInferenceSelectedExpressionList

/-! Builtin calls use their fixed signatures and the actual synthetic callee.
Only the descendant records of the call are needed in the semantic carrier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

private def builtinMetadata (state : State) :=
  (state.owner, state.integerPatterns, state.integerLiterals)

private theorem unify_builtinMetadata {state next : State} {left right : Ty}
    (success : Detail.unify state left right = .ok next) :
    builtinMetadata next = builtinMetadata state := by
  unfold Detail.unify at success
  cases unified : state.inference.unify left right <;>
    simp [Detail.liftUnification, unified, bind, Except.bind] at success
  cases success
  rfl

private theorem unifyBuiltinArguments_metadata
    {arguments : List InferredExpression} {parameters : List Ty} {state next : State}
    (success : Detail.unifyBuiltinFunctionArgumentsEqual arguments parameters state = .ok next) :
    builtinMetadata next = builtinMetadata state := by
  induction arguments generalizing parameters state next with
  | nil =>
    simp only [Detail.unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at success
    subst next
    rfl
  | cons argument arguments induction =>
    cases parameters with
    | nil =>
      simp only [Detail.unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at success
      subst next
      rfl
    | cons parameter parameters =>
      simp only [Detail.unifyBuiltinFunctionArgumentsEqual] at success
      cases unified : Detail.unify state argument.type parameter with
      | error error => simp [unified, bind, Except.bind] at success
      | ok unifiedState =>
        simp only [unified, bind, Except.bind] at success
        exact (induction success).trans (unify_builtinMetadata unified)

theorem recordBuiltinFunctionCall_metadata
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : Detail.recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result) :
    result.2.owner = state.owner ∧ result.2.integerPatterns = state.integerPatterns ∧
      result.2.integerLiterals = state.integerLiterals := by
  have metadata : builtinMetadata result.2 = builtinMetadata state := by
    unfold Detail.recordBuiltinFunctionCall at success
    by_cases arity : arguments.length = function.parameterTypes.length
    · simp only [arity, ↓reduceIte, bind, Except.bind] at success
      cases fitted : Detail.unifyBuiltinFunctionArgumentsEqual arguments function.parameterTypes state with
      | error error => simp [fitted] at success
      | ok fittedState =>
        simp only [fitted] at success
        have fittedMetadata := unifyBuiltinArguments_metadata fitted
        cases expected with
        | none =>
          simp only [pure, Except.pure, Except.ok.injEq] at success
          subst result
          exact fittedMetadata
        | some expected =>
          cases unified : Detail.unify fittedState function.returnType expected with
          | error error => simp [unified] at success
          | ok unifiedState =>
            simp only [unified, pure, Except.pure, Except.ok.injEq] at success
            subst result
            exact (unify_builtinMetadata unified).trans fittedMetadata
    · simp [arity, bind, Except.bind] at success
  exact ⟨congrArg Prod.fst metadata, congrArg (fun row => row.2.1) metadata,
    congrArg (fun row => row.2.2) metadata⟩

theorem recordBuiltinFunctionCall_expressionTypingBase_actual
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {recorded : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {semanticSource : TypedSource}
    {active : SourceSemantics.Context}
    {substitution : TypeSystem.Substitution}
    (success : Detail.recordBuiltinFunctionCall source callee name function
      arguments call expected state = .ok recorded)
    (substitutionExtends : substitution.SemanticallyExtends
      recorded.2.inference.substitution)
    (preserved : ProperDescendantsPreserved substitution
      (recorded.2.toTypedSource roots) semanticSource (.expression recorded.1.id))
    (argumentsType : ExpressionsHaveTypes semanticSource active
      (arguments.map (·.id))
      (arguments.map fun argument => substitution.apply argument.type))
    (binders : TypeParameterBindersWellFormed active) :
    ExpressionTypingBase (recorded.2.toTypedSource roots) semanticSource
      active substitution recorded.1 := by
  obtain ⟨calleeId, nodesEq⟩ :=
    Detail.recordBuiltinFunctionCall_success_nodes success
  let calleeNode : ExpressionNode := {
    id := calleeId
    span := callee.span
    type := function.type
    form := .reference name (.builtinFunction function)
  }
  let callNode : ExpressionNode := {
    id := recorded.1.id
    span := source.span
    type := recorded.1.type
    form := .call calleeId (arguments.map (·.id))
      (.builtinFunction function)
  }
  have rawCalleeContains : ContainsExpression
      (recorded.2.toTypedSource roots) calleeId calleeNode := by
    refine ⟨?_, rfl⟩
    change .expression calleeNode ∈ recorded.2.nodes
    rw [nodesEq]
    simp [calleeNode]
  have rawCallContains : ContainsExpression
      (recorded.2.toTypedSource roots) recorded.1.id callNode := by
    refine ⟨?_, rfl⟩
    change .expression callNode ∈ recorded.2.nodes
    rw [nodesEq]
    simp [callNode]
  have calleeEdge : DirectChild (recorded.2.toTypedSource roots)
      (.expression recorded.1.id) (.expression calleeId) := by
    refine ⟨.expression callNode, ⟨rawCallContains.1, rfl⟩, ?_⟩
    simp [callNode, nodeChildIds, Node.references, ExpressionForm.references]
  have finalCalleeContains : ContainsExpression semanticSource calleeId
      (calleeNode.applySubstitution substitution) :=
    (preserved.childSubtree calleeEdge).subgraph.containsExpression
      (FlexibleSubstitution.ContainsExpression.applySubstitution substitution rawCalleeContains) (.inl rfl)
  have calleeValid : DirectBuiltinCalleeValid semanticSource calleeId
      function := by
    refine .intro (name := name) finalCalleeContains ?_ ?_ ?_ ?_
    · rfl
    · cases function <;> rfl
    · rfl
    · rfl
  have argumentTypesEq :=
    Detail.recordBuiltinFunctionCall_success_argumentTypes_apply_eq success
      substitutionExtends
  have finalArgumentsType : ExpressionsHaveTypes semanticSource active
      (arguments.map (·.id)) function.parameterTypes := by
    rw [← argumentTypesEq]
    exact argumentsType
  have formType : ExpressionFormHasRawType semanticSource active
      (callNode.applySubstitution substitution).form function.returnType
      (.ordinary []) := by
    simpa [callNode, ExpressionNode.applySubstitution,
      ExpressionForm.applySubstitution, CallResolution.applySubstitution] using
        (ExpressionFormHasRawType.builtinCall calleeValid finalArgumentsType)
  have rawAdmissible : TypeAdmissible active function.returnType :=
    TypeAdmissible.builtinFunctionResult binders function
  have resultTypeEq :=
    Detail.recordBuiltinFunctionCall_success_returnType_eq success
  have finalTypeEq : substitution.apply recorded.1.type =
      function.returnType := by
    rw [resultTypeEq]
    cases function <;> rfl
  refine .intro rawCallContains rfl formType rawAdmissible ?_
  apply ExpressionRequirementPlan.Valid.ordinary
  · simp [RequirementIdsValid]
  · change CoercionPathValid active function.returnType
      (substitution.apply recorded.1.type) []
    rw [finalTypeEq]
    exact .nil _
  · rfl


theorem actualBuiltinCall_typing {fuel : Nat}
    (recursive : ∀ smaller, smaller < fuel → ActualInferExprFuelRetainedSoundness smaller) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression callee : Syntax.Expr} {expected : Option Ty}
    {argumentSources : List Syntax.Expr} {arguments : List InferredExpression}
    {name : String} {function : BuiltinFunctionId} {call : ExpressionId}
    {initial argumentState resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    Detail.inferExprsFuel fuel inferenceContext argumentSources initial = .ok (arguments, argumentState) →
    Detail.recordBuiltinFunctionCall expression callee name function arguments
      call expected argumentState = .ok (inferred, resultState) →
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
    name function call initial argumentState resultState evidenceState
    inferred roots finalized semanticSource frames semanticContext argumentsSuccess
    recording resources interfaces resultSubstitutionExtension signaturesEq ownerEq
    typeParametersEq assumptionsEq signatureFormation functionsCanonical catalog canonical invariant
    actual operational expectedBelow expectedAdmissible finalPreserved rawProper integerPatternsSubset
    integerLiteralsSubset requirementsSubset retained coercionsRetained _operatorsRetained childrenRetained covered
    semanticPreserved actualCovered
  have argumentProperties := Detail.inferExprsFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical argumentsSuccess
  have expectedAtArguments : ∀ type ∈ expected, type.VariablesBelow argumentState.inference.next :=
    fun type member => (expectedBelow type member).weaken argumentProperties.1.next_le
  have recordProperties := Detail.recordBuiltinFunctionCall_inferenceProperties
    argumentProperties.2.1 argumentProperties.2.2 expectedAtArguments recording
  have argumentExtension := resultSubstitutionExtension.trans recordProperties.1.substitution_extends
  have metadata := recordBuiltinFunctionCall_metadata recording
  obtain ⟨calleeId, nodesEq⟩ := Detail.recordBuiltinFunctionCall_success_nodes recording
  have argumentToParent : TypingSourceExtends (argumentState.toTypedSource roots)
      (resultState.toTypedSource roots) := by
    refine ⟨metadata.1, ?_⟩
    change argumentState.nodes <+: resultState.nodes
    rw [nodesEq]
    exact List.prefix_append _ _
  let callNode : ExpressionNode := {
    id := inferred.id
    span := expression.span
    type := inferred.type
    form := .call calleeId (arguments.map (·.id)) (.builtinFunction function)
  }
  have callContains : ContainsExpression (resultState.toTypedSource roots) inferred.id callNode := by
    refine ⟨?_, rfl⟩
    change .expression callNode ∈ resultState.nodes
    rw [nodesEq]
    simp [callNode]
  have argumentEdge : ∀ argument ∈ arguments,
      DirectChild (resultState.toTypedSource roots) (.expression inferred.id) (.expression argument.id) := by
    intro argument member
    refine ⟨.expression callNode, ⟨callContains.1, rfl⟩, ?_⟩
    simp only [callNode, nodeChildIds, Node.references, ExpressionForm.references, List.mem_cons]
    exact Or.inr (List.mem_map.mpr ⟨argument.id, List.mem_map.mpr ⟨argument, member, rfl⟩, rfl⟩)
  have argumentPatterns : argumentState.integerPatterns ⊆ evidenceState.integerPatterns := by
    rw [← metadata.2.1]
    exact integerPatternsSubset
  have argumentLiterals : argumentState.integerLiterals ⊆ evidenceState.integerLiterals := by
    rw [← metadata.2.2]
    exact integerLiteralsSubset
  have argumentRequirements := List.Subset.trans
    (Detail.recordBuiltinFunctionCall_requirements_subset recording) requirementsSubset
  have argumentsTyped := actualInferExprsFuelFinalSubtreeSoundness fuel recursive
    argumentsSuccess resources interfaces argumentExtension signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical invariant actual operational
    (fun argument member => (semanticPreserved.childSubtree (argumentEdge argument member)).monoBefore argumentToParent)
    (fun argument member => (finalPreserved.childSubtree (argumentEdge argument member)).monoBefore argumentToParent)
    (fun argument member => ((rawProper.childSubtree (argumentEdge argument member)).monoBefore argumentToParent).proper)
    argumentPatterns argumentLiterals argumentRequirements
    (fun argument member => covered.expressionChild resources.graph_closed (childrenRetained (argumentEdge argument member)))
    (fun argument member => actualCovered.directChild (childrenRetained (argumentEdge argument member)))
  exact recordBuiltinFunctionCall_expressionTypingBase_actual recording resultSubstitutionExtension
    semanticPreserved argumentsTyped
    (invariant.typeParameterBinders (by simpa only [ownerEq, typeParametersEq] using canonical))

end Solcore.SourceSemantics.SourceInferenceSoundness
