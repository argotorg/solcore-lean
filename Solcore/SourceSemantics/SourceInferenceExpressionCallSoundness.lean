import Solcore.SourceSemantics.SourceInferenceExpressionDispatchSoundness

/-!
Operationally bounded call-inference bridges.  Selected calls may rewrite
their argument nodes when attaching coercions, so argument typing is first
established against the exact pre-selection argument state rather than against
an unrelated, later node table.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend SourceInference TypeSystem

/-- Actual argument and callee inference traces yield ordinary typing in the
finalized source.  The append-only and ledger premises identify the finalizer
input with this call's real child states; the callback can therefore be used
only at children of the enclosing expression. -/
theorem inferExprsFuel_inferExprFuel_success_childrenHaveTypes_under_ambient_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {argumentSources : List Syntax.Expr}
    {argumentInitial argumentState calleeState finalInput :
      Frontend.SourceInference.State}
    {arguments : List InferredExpression}
    {calleeSource : Syntax.Expr} {callee : InferredExpression}
    {finalType : TypeSystem.Ty} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {sourceContext active : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (fuel_lt : fuel < parentFuel)
    (argumentsSuccess : Detail.inferExprsFuel fuel inferenceContext
      argumentSources argumentInitial = .ok (arguments, argumentState))
    (calleeSuccess : Detail.inferExprFuel fuel inferenceContext calleeSource
      none argumentState = .ok (callee, calleeState))
    (resources : FinalInferenceResources inferenceContext finalType
      finalInput roots finalized)
    (initialBelow : argumentInitial.NodesBelowNextOccurrence)
    (argumentToFinalInput : TypingSourceExtends
      (argumentState.toTypedSource roots) (finalInput.toTypedSource roots))
    (calleeToFinalInput : TypingSourceExtends
      (calleeState.toTypedSource roots) (finalInput.toTypedSource roots))
    (argumentIntegerPatternsSubset :
      argumentState.integerPatterns ⊆ finalInput.integerPatterns)
    (argumentIntegerSubset :
      argumentState.integerLiterals ⊆ finalInput.integerLiterals)
    (argumentRequirementsSubset :
      argumentState.requirements ⊆ finalInput.requirements)
    (calleeIntegerSubset :
      calleeState.integerLiterals ⊆ finalInput.integerLiterals)
    (calleeIntegerPatternsSubset :
      calleeState.integerPatterns ⊆ finalInput.integerPatterns)
    (calleeRequirementsSubset :
      calleeState.requirements ⊆ finalInput.requirements)
    (childSound : ExpressionChildTypingCallback parentFuel inferenceContext
      (finalInput.toTypedSource roots) finalized.typedSource finalInput active
      finalized.substitution roots)
    (binders : TypeParameterBindersWellFormed sourceContext)
    (signaturesEq : sourceContext.signatures =
      inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active) :
    ExpressionsHaveTypes finalized.typedSource active
        (arguments.map (·.id))
        (arguments.map fun argument =>
          finalized.substitution.apply argument.type) ∧
      ExpressionHasType finalized.typedSource active callee.id
        (finalized.substitution.apply callee.type) := by
  have argumentBases :=
    inferExprsFuel_success_argumentTypingBasesValid_under_ambient_bounded
      (roots := roots) fuel_lt initialBelow argumentToFinalInput
      argumentIntegerPatternsSubset argumentIntegerSubset
      argumentRequirementsSubset childSound argumentsSuccess
  have argumentsTyped :=
    resources.expressionsHaveTypes_of_argumentTypingBases_prefix
      argumentBases argumentToFinalInput binders signaturesEq parametersEq
      ownerEq residual contextValid
  have argumentStateBelow : argumentState.NodesBelowNextOccurrence :=
    (Detail.inferExprsFuel_occurrenceBoundExtends argumentsSuccess
      ).nodesBelowNextOccurrence initialBelow
  let calleeChild : ExpressionChildInferenceProvenance parentFuel
      inferenceContext (finalInput.toTypedSource roots) finalInput roots := {
    fuel := fuel
    expression := calleeSource
    expected := none
    initial := argumentState
    final := calleeState
    inferred := callee
    fuel_lt := fuel_lt
    initialNodesBelow := argumentStateBelow
    success := calleeSuccess
    sourceExtension := calleeToFinalInput
    integerPatternsSubset := calleeIntegerPatternsSubset
    integerLiteralsSubset := calleeIntegerSubset
    requirementsSubset := calleeRequirementsSubset
  }
  have calleeBase := childSound calleeChild
  have calleeBaseAtFinalInput :=
    calleeBase.weakenNodeSource calleeToFinalInput.nodes_prefix
  have calleeTyped := resources.expressionHasType_of_typingBase
    calleeBaseAtFinalInput binders signaturesEq parametersEq ownerEq residual
    contextValid
  exact ⟨argumentsTyped, calleeTyped⟩

/-- A builtin call is typed from the exact argument traversal that precedes
its recorder, with no hypothetical unrelated argument-inference callback. -/
theorem inferExprsFuel_recordBuiltinFunctionCall_success_expressionTypingBase_under_ambient_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : TypeSystem.Ty}
    {resultState evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {argumentSources : List Syntax.Expr}
    {argumentInitial argumentState : Frontend.SourceInference.State}
    {arguments : List InferredExpression}
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {call : ExpressionId}
    {expected : Option TypeSystem.Ty} {inferred : InferredExpression}
    {sourceContext active : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (fuel_lt : fuel < parentFuel)
    (argumentsSuccess : Detail.inferExprsFuel fuel inferenceContext
      argumentSources argumentInitial = .ok (arguments, argumentState))
    (recordSuccess : Detail.recordBuiltinFunctionCall source callee name
      function arguments call expected argumentState =
        .ok (inferred, resultState))
    (initialBelow : argumentInitial.NodesBelowNextOccurrence)
    (argumentToResult : TypingSourceExtends
      (argumentState.toTypedSource roots) (resultState.toTypedSource roots))
    (resultToEvidence : TypingSourceExtends
      (resultState.toTypedSource roots) (evidenceState.toTypedSource roots))
    (argumentIntegerPatternsSubset :
      argumentState.integerPatterns ⊆ resultState.integerPatterns)
    (argumentIntegerSubset :
      argumentState.integerLiterals ⊆ resultState.integerLiterals)
    (argumentRequirementsSubset :
      argumentState.requirements ⊆ resultState.requirements)
    (resultIntegerSubset :
      resultState.integerLiterals ⊆ evidenceState.integerLiterals)
    (resultIntegerPatternsSubset :
      resultState.integerPatterns ⊆ evidenceState.integerPatterns)
    (resultRequirementsSubset :
      resultState.requirements ⊆ evidenceState.requirements)
    (childSound : ExpressionChildTypingCallback parentFuel inferenceContext
      (evidenceState.toTypedSource roots) finalized.typedSource evidenceState active
      finalized.substitution roots)
    (substitutionExtends : finalized.substitution.SemanticallyExtends
      resultState.inference.substitution)
    (binders : TypeParameterBindersWellFormed sourceContext)
    (activeBinders : TypeParameterBindersWellFormed active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active) :
    ExpressionTypingBase (resultState.toTypedSource roots)
      finalized.typedSource active finalized.substitution inferred := by
  have argumentToEvidence : TypingSourceExtends
      (argumentState.toTypedSource roots)
      (evidenceState.toTypedSource roots) :=
    argumentToResult.trans resultToEvidence
  have argumentBases :=
    inferExprsFuel_success_argumentTypingBasesValid_under_ambient_bounded
      (roots := roots) fuel_lt initialBelow argumentToEvidence
      (List.Subset.trans argumentIntegerPatternsSubset
        resultIntegerPatternsSubset)
      (List.Subset.trans argumentIntegerSubset resultIntegerSubset)
      (List.Subset.trans argumentRequirementsSubset resultRequirementsSubset)
      childSound
      argumentsSuccess
  have argumentTypes :=
    resources.expressionsHaveTypes_of_argumentTypingBases_prefix
      argumentBases argumentToEvidence binders signaturesEq parametersEq
      ownerEq residual contextValid
  have sourceExtension : TypingSourceExtends
      ((resultState.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource := by
    rw [resources.source_eq]
    exact resultToEvidence.applySubstitution finalized.substitution
  exact recordBuiltinFunctionCall_success_expressionTypingBase recordSuccess
    substitutionExtends sourceExtension argumentTypes activeBinders

/-- The arguments of an actually selected direct call are sound under a
bounded, parent-linked recursive expression hypothesis.  Unlike the older
callback theorem, this does not quantify over unrelated successful child
inferences: the only children inspected are those in `argumentsSuccess`. -/
theorem
    inferExprsFuel_selectFunctionCandidateFrom_recordSelectedCall_success_expressionTypingBase_under_ambient_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {argumentSources : List Syntax.Expr}
    {argumentInitial argumentState : Frontend.SourceInference.State}
    {arguments : List InferredExpression}
    {source callee : Syntax.Expr} {name : String}
    {candidates : List ProgramFunctionSignature}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {attempt : Detail.CandidateAttemptResult}
    {result : InferredExpression}
    {resultState later : Frontend.SourceInference.State}
    {roots : List NodeId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext base active : SourceSemantics.Context}
    {ledgerSource : TypedSource}
    {closedVariables : List TypeSystem.TypeVarId}
    (fuel_lt : fuel < parentFuel)
    (argumentsSuccess : Detail.inferExprsFuel fuel inferenceContext
      argumentSources argumentInitial = .ok (arguments, argumentState))
    (selectionSuccess : Detail.selectFunctionCandidateFrom inferenceContext
      name candidates arguments integerLiteralOrigins call expected
      argumentState = .ok attempt)
    (recordEq : Detail.recordSelectedCall source callee name arguments attempt =
      (result, resultState))
    (candidatesSubset : candidates ⊆
      inferenceContext.signatures.functions)
    (argumentInitialReady : argumentInitial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow argumentInitial.inference.next)
    (nodesBelow : argumentInitial.NodesBelowNextOccurrence)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ later.requirements)
    (sourceExtension : TypingSourceExtends
      ((resultState.toTypedSource roots).applySubstitution
        later.inference.substitution) ledgerSource)
    (childSound : ExpressionChildTypingCallback parentFuel inferenceContext
      (argumentState.toTypedSource roots) ledgerSource argumentState active
      later.inference.substitution roots)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (binders : TypeParameterBindersWellFormed sourceContext)
    (residual : sourceContext.residualTypeVariables = true)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures =
      inferenceContext.signatures)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements inferenceContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (graphClosed : OccurrenceGraphClosed ledgerSource)
    (callCovered : TemplateScopeCovered ledgerSource active
      (.expression result.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) ledgerSource active
      later.inference.substitution result := by
  have argumentProperties := Detail.inferExprsFuel_inferenceProperties
    argumentInitialReady signatureFormation functionsCanonical argumentsSuccess
  have expectedAtArguments : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow argumentState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      argumentProperties.1.next_le
  have bases :=
    inferExprsFuel_success_argumentTypingBasesValid_under_ambient_bounded
      (roots := roots) fuel_lt nodesBelow
      (TypingSourceExtends.refl _) (by intro _ member; exact member)
      (by intro _ member; exact member)
      (by intro _ member; exact member) childSound argumentsSuccess
  have argumentIdsUnique :=
    Detail.inferExprsFuel_success_ids_nodup argumentsSuccess
  obtain ⟨signature, _, signatureMember, canonical, schemeBodyBelow,
      candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_semanticCandidate signatureFormation
      functionsCanonical signaturesEq candidatesSubset selectionSuccess
  have candidateProperties :=
    Detail.tryFunctionCandidate_some_inferenceProperties
      argumentProperties.2.1 argumentProperties.2.2 schemeBodyBelow
      expectedAtArguments candidateSuccess
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
    tryFunctionCandidate_some_recordSelectedCallResult_success_expressionTypingBase_scoped
      canonical candidateSuccess recordSuccess rfl rfl bases
      argumentIdsUnique argumentProperties.2.1 argumentProperties.2.2
      schemeBodyBelow expectedAtArguments laterExtendsAttempt
      laterExtendsAttempt attemptRequirementsAtLater sourceExtension catalog
      binders residual signatureMember contextValid signaturesEq
      traitSuccess profileSuccess traitName solveSuccess
      solvedEq ledger ownership activeSignaturesEq activeRequirementsEq
      assumptionsMono graphClosed callCovered (.nil _)

/-- Indirect-call soundness with recursive hypotheses confined to the actual
argument and callee traces.  Finalization converts those bounded child bases
to declarative typing before the call-specific coercion proof runs. -/
theorem
    inferExprsFuel_inferExprFuel_applyFunctionType_recordIndirectCall_success_expressionTypingBase_under_ambient_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {argumentSources : List Syntax.Expr}
    {argumentInitial argumentState calleeState resultState later finalInput :
      Frontend.SourceInference.State}
    {arguments : List InferredExpression}
    {source calleeSource : Syntax.Expr}
    {callee : InferredExpression}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {application : Detail.IndirectApplicationResult}
    {result : InferredExpression}
    {roots : List NodeId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext base active : SourceSemantics.Context}
    {ledgerSource : TypedSource}
    {closedVariables : List TypeSystem.TypeVarId}
    {finalType : TypeSystem.Ty}
    {finalized : Frontend.SourceInference.Result}
    (fuel_lt : fuel < parentFuel)
    (argumentsSuccess : Detail.inferExprsFuel fuel inferenceContext
      argumentSources argumentInitial = .ok (arguments, argumentState))
    (calleeSuccess : Detail.inferExprFuel fuel inferenceContext calleeSource
      none argumentState = .ok (callee, calleeState))
    (applicationSuccess : Detail.applyFunctionType inferenceContext call
      callee.type arguments expected calleeState = .ok application)
    (recordEq : Detail.recordIndirectCall source callee arguments application =
      (result, resultState))
    (resources : FinalInferenceResources inferenceContext finalType
      finalInput roots finalized)
    (finalSourceEq : finalized.typedSource = ledgerSource)
    (finalSubstitutionEq :
      finalized.substitution = later.inference.substitution)
    (initialBelow : argumentInitial.NodesBelowNextOccurrence)
    (argumentToFinalInput : TypingSourceExtends
      (argumentState.toTypedSource roots) (finalInput.toTypedSource roots))
    (calleeToFinalInput : TypingSourceExtends
      (calleeState.toTypedSource roots) (finalInput.toTypedSource roots))
    (argumentIntegerPatternsSubset :
      argumentState.integerPatterns ⊆ finalInput.integerPatterns)
    (argumentIntegerSubset :
      argumentState.integerLiterals ⊆ finalInput.integerLiterals)
    (argumentRequirementsSubset :
      argumentState.requirements ⊆ finalInput.requirements)
    (calleeIntegerSubset :
      calleeState.integerLiterals ⊆ finalInput.integerLiterals)
    (calleeIntegerPatternsSubset :
      calleeState.integerPatterns ⊆ finalInput.integerPatterns)
    (calleeRequirementsSubset :
      calleeState.requirements ⊆ finalInput.requirements)
    (childSound : ExpressionChildTypingCallback parentFuel inferenceContext
      (finalInput.toTypedSource roots) finalized.typedSource finalInput active
      finalized.substitution roots)
    (applicationReady : calleeState.InferenceReady)
    (calleeBelow : callee.type.VariablesBelow
      calleeState.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow calleeState.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow calleeState.inference.next)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ later.requirements)
    (sourceExtension : TypingSourceExtends
      ((resultState.toTypedSource roots).applySubstitution
        later.inference.substitution) ledgerSource)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (binders : TypeParameterBindersWellFormed sourceContext)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements inferenceContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (callCovered : TemplateScopeCovered ledgerSource active
      (.expression result.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) ledgerSource active
      later.inference.substitution result := by
  obtain ⟨argumentTyping, calleeTyping⟩ :=
    inferExprsFuel_inferExprFuel_success_childrenHaveTypes_under_ambient_bounded
      fuel_lt argumentsSuccess calleeSuccess resources initialBelow
      argumentToFinalInput calleeToFinalInput argumentIntegerPatternsSubset
      argumentIntegerSubset argumentRequirementsSubset calleeIntegerSubset
      calleeIntegerPatternsSubset calleeRequirementsSubset childSound binders
      signaturesEq parametersEq ownerEq residual contextValid
  have argumentTypingAtLater : ExpressionsHaveTypes ledgerSource active
      (arguments.map (·.id))
      (arguments.map fun argument =>
        later.inference.substitution.apply argument.type) := by
    simpa only [finalSourceEq, finalSubstitutionEq] using argumentTyping
  have calleeTypingAtLater : ExpressionHasType ledgerSource active callee.id
      (later.inference.substitution.apply callee.type) := by
    simpa only [finalSourceEq, finalSubstitutionEq] using calleeTyping
  have contextValidAtLater :
      FlexibleSubstitution.ContextSubstitutionValid
        later.inference.substitution closedVariables sourceContext active := by
    simpa only [finalSubstitutionEq] using contextValid
  exact
    inferExprsFuel_inferExprFuel_applyFunctionType_recordIndirectCall_success_expressionTypingBase_from_children
      argumentsSuccess calleeSuccess applicationSuccess recordEq
      applicationReady calleeBelow argumentsBelow expectedBelow
      substitutionExtends requirementsSubset sourceExtension
      argumentTypingAtLater calleeTypingAtLater traitSuccess
      profileSuccess catalog contextValidAtLater signaturesEq traitName
      solveSuccess solvedEq ledger ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono callCovered

end Solcore.SourceSemantics.SourceInferenceSoundness
