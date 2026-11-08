import Solcore.SourceSemantics.Internal.Inference.ExpressionDispatch
import Solcore.SourceSemantics.Internal.Inference.StatementResources

/-!
# Calls and operators in expression inference

Inversion of source calls, bounded bridges for calls and operators, and the fuel-recursive
expression theorem.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceExpressionCallSoundness
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceExpressionCallDispatchSoundness
/-!
Top-level operational inversion for source call expressions.

The call implementation contains several pieces of name-resolution control
flow before reaching one of the four semantic tails.  This module records
only the successful tail which was actually executed.  In particular, the
selected-call case retains whether its candidate row came from qualified or
unqualified lookup, so catalog membership is recovered without a hypothetical
lookup premise.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend SourceInference TypeSystem

/-- Every outgoing occurrence edge of one expression root survives in an
eventual evidence source.  This permits selected-call attachment to rewrite
the root's type and coercion metadata while retaining its expression form. -/
def ExpressionDirectChildrenRetainedAt
    (before after : TypedSource) (parent : ExpressionId) : Prop :=
  ∀ {child : NodeId},
    DirectChild before (.expression parent) child →
      DirectChild after (.expression parent) child

namespace ExpressionDirectChildrenRetainedAt

theorem trans
    {first second third : TypedSource} {parent : ExpressionId}
    (left : ExpressionDirectChildrenRetainedAt first second parent)
    (right : ExpressionDirectChildrenRetainedAt second third parent) :
    ExpressionDirectChildrenRetainedAt first third parent := by
  intro child edge
  exact right (left edge)

/-- Exact node-table equality preserves all outgoing expression edges. -/
theorem ofNodesEq
    {before after : TypedSource} {parent : ExpressionId}
    (nodesEq : after.nodes = before.nodes) :
    ExpressionDirectChildrenRetainedAt before after parent := by
  intro child edge
  rcases edge with ⟨node, contains, member⟩
  exact ⟨node, ⟨by rw [nodesEq]; exact contains.1, contains.2⟩, member⟩

/-- A raw append-only prefix may precede any eventual retained edge map. -/
theorem monoBefore
    {before middle after : TypedSource} {parent : ExpressionId}
    (extension : TypingSourceExtends before middle)
    (retained : ExpressionDirectChildrenRetainedAt middle after parent) :
    ExpressionDirectChildrenRetainedAt before after parent := by
  intro child edge
  rcases edge with ⟨node, contains, member⟩
  apply retained
  exact ⟨node,
    ⟨extension.nodes_prefix.subset contains.1, contains.2⟩, member⟩

/-- Exact preservation of a substituted expression node preserves all of its
form references, and hence every direct child edge. -/
theorem ofExpressionNodesPreservedAt
    {before after : TypedSource} {parent : ExpressionId}
    {substitution : TypeSystem.Substitution}
    (preserved : ExpressionNodesPreservedAt [parent]
      (before.applySubstitution substitution) after) :
    ExpressionDirectChildrenRetainedAt before after parent := by
  intro child edge
  have substitutedEdge :=
    FlexibleSubstitution.directChild_applySubstitution substitution edge
  rcases substitutedEdge with ⟨node, contains, childMember⟩
  cases node with
  | statement statementNode =>
      have impossible : (NodeId.statement statementNode.id) =
          .expression parent := contains.2
      cases impossible
  | expression expressionNode =>
      have parentIdEq : expressionNode.id = parent := by
        have wrapped : NodeId.expression expressionNode.id =
            .expression parent := contains.2
        injection wrapped
      have expressionContains : ContainsExpression
          (before.applySubstitution substitution) parent expressionNode :=
        ⟨contains.1, parentIdEq⟩
      have finalContains : ContainsExpression after parent expressionNode :=
        preserved (by simp) expressionContains
      exact ⟨.expression expressionNode,
        ⟨finalContains.1, congrArg NodeId.expression finalContains.2⟩,
        childMember⟩

theorem ofTypingSourceExtends
    {before after : TypedSource} {parent : ExpressionId}
    (substitution : TypeSystem.Substitution)
    (extension : TypingSourceExtends
      (before.applySubstitution substitution) after) :
    ExpressionDirectChildrenRetainedAt before after parent := by
  exact ofExpressionNodesPreservedAt
    (ExpressionNodesPreservedAt.ofTypingSourceExtends extension)

/-- Delayed-coercion attachment preserves expression forms and their child
references even at roots whose type and requirement rows are rewritten. -/
theorem ofAttachExpressionCoercions
    (state : Frontend.SourceInference.State)
    (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) (parent : ExpressionId) :
    ExpressionDirectChildrenRetainedAt (state.toTypedSource roots)
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots)
      parent := by
  induction entries generalizing state with
  | nil =>
      intro child edge
      simpa [Detail.attachExpressionCoercions] using edge
  | cons entry entries induction =>
      let next := state.modifyExpressionNode entry.expression fun node =>
        Detail.appendExpressionCoercions node entry.coercions
      have step : ExpressionDirectChildrenRetainedAt
          (state.toTypedSource roots) (next.toTypedSource roots) parent := by
        intro child edge
        rcases edge with ⟨node, contains, childMember⟩
        cases node with
        | statement statementNode =>
            have impossible : (NodeId.statement statementNode.id) =
                .expression parent := contains.2
            cases impossible
        | expression expressionNode =>
            have parentIdEq : expressionNode.id = parent := by
              have wrapped : NodeId.expression expressionNode.id =
                  .expression parent := contains.2
              injection wrapped
            have expressionContains : ContainsExpression
                (state.toTypedSource roots) parent expressionNode :=
              ⟨contains.1, parentIdEq⟩
            by_cases targetEq : parent = entry.expression
            · have expressionTargetEq : expressionNode.id =
                  entry.expression := parentIdEq.trans targetEq
              have targetContains : ContainsExpression
                  (state.toTypedSource roots) entry.expression
                  expressionNode := ⟨contains.1, expressionTargetEq⟩
              have modifiedContains :=
                modifyExpressionNode_containsExpression_self state
                  entry.expression expressionNode
                  (fun node => Detail.appendExpressionCoercions node
                    entry.coercions)
                  roots targetContains
              let modifiedNode : ExpressionNode := {
                Detail.appendExpressionCoercions expressionNode
                    entry.coercions with
                id := entry.expression
              }
              refine ⟨.expression modifiedNode,
                ⟨modifiedContains.1, ?_⟩, ?_⟩
              · exact (congrArg NodeId.expression modifiedContains.2).trans
                  (congrArg NodeId.expression targetEq.symm)
              simpa [modifiedNode, Detail.appendExpressionCoercions,
                nodeChildIds, Node.references] using childMember
            · have modifiedContains :=
                modifyExpressionNode_containsExpression_other state
                  entry.expression parent expressionNode
                  (fun node => Detail.appendExpressionCoercions node
                    entry.coercions)
                  roots targetEq expressionContains
              exact ⟨.expression expressionNode,
                ⟨modifiedContains.1,
                  congrArg NodeId.expression modifiedContains.2⟩,
                childMember⟩
      change ExpressionDirectChildrenRetainedAt (state.toTypedSource roots)
        ((Detail.attachExpressionCoercions next entries).toTypedSource roots)
        parent
      exact step.trans (induction (state := next))

end ExpressionDirectChildrenRetainedAt

/-- Operational provenance for the candidate row of a selected direct call. -/
inductive SelectedCallCandidatesOrigin
    (context : Frontend.SourceInference.Context) :
    String → List ProgramFunctionSignature → Prop where
  | unqualified
      {name : String} {candidates : List ProgramFunctionSignature}
      (lookup : Detail.functionsNamed context name = .ok candidates) :
      SelectedCallCandidatesOrigin context name candidates
  | qualified
      {namespacePath : List String} {name : String}
      {candidates : List ProgramFunctionSignature}
      (lookup : Detail.qualifiedFunctionsNamed context namespacePath name =
        .ok (some candidates)) :
      SelectedCallCandidatesOrigin context
        (String.intercalate "." (namespacePath ++ [name])) candidates

theorem SelectedCallCandidatesOrigin.candidatesSubset
    {context : Frontend.SourceInference.Context}
    {name : String} {candidates : List ProgramFunctionSignature}
    (origin : SelectedCallCandidatesOrigin context name candidates) :
    candidates ⊆ context.signatures.functions := by
  cases origin with
  | unqualified lookup =>
      exact Detail.functionsNamed_success_subset_catalog lookup
  | qualified lookup =>
      exact Detail.qualifiedFunctionsNamed_success_subset_catalog lookup

/-- Recursive expression soundness at a node which may subsequently be
rewritten by delayed coercion attachment.  The ordinary bounded callback
uses an append-only ambient node source; selected-call arguments instead
carry occurrence-scoped requirement retention into the eventual evidence
source.  The operational provenance still ties every invocation to the
enclosing computation and its final ledgers. -/
def RetainedExpressionChildTypingCallback
    (parentFuel : Nat)
    (inferenceContext : Frontend.SourceInference.Context)
    (ambientNodeSource semanticSource evidenceSource : TypedSource)
    (evidenceState : Frontend.SourceInference.State)
    (context : SourceSemantics.Context)
    (substitution : TypeSystem.Substitution)
    (roots : List NodeId) : Prop :=
  ∀ child : ExpressionChildInferenceProvenance parentFuel inferenceContext
      ambientNodeSource evidenceState roots,
    ExpressionRequirementsRetainedAt (child.final.toTypedSource roots)
        evidenceSource child.inferred.id →
      ExpressionTypingBase (child.final.toTypedSource roots) semanticSource
        context substitution child.inferred

/-- The recursive boundary needed by a closed whole-body theorem.  Besides
operational provenance and requirement retention, every invocation carries
both the final scope-coverage fact and preservation of every raw outgoing
edge of that actual child occurrence.  Coverage is not implied by source
extension; the enclosing expression form supplies it from its concrete
direct-child edge and the final closed occurrence graph.  Edge preservation
is the extra invariant needed across selected-call coercion attachment, which
may rewrite the child root without changing its form or references. -/
def CoveredRetainedExpressionChildTypingCallback
    (parentFuel : Nat)
    (inferenceContext : Frontend.SourceInference.Context)
    (ambientNodeSource semanticSource evidenceSource : TypedSource)
    (evidenceState : Frontend.SourceInference.State)
    (context : SourceSemantics.Context)
    (substitution : TypeSystem.Substitution)
    (roots : List NodeId) : Prop :=
  ∀ child : ExpressionChildInferenceProvenance parentFuel inferenceContext
      ambientNodeSource evidenceState roots,
    child.initial.InferenceReady →
      (∀ expectedType ∈ child.expected,
        expectedType.VariablesBelow child.initial.inference.next) →
      ActiveLocalContextInvariant child.initial substitution context →
      child.initial.LocalBindersBelowNextLocal →
      ExpressionRequirementsRetainedAt (child.final.toTypedSource roots)
          evidenceSource child.inferred.id →
        ExpressionDirectChildrenRetainedAt (child.final.toTypedSource roots)
            evidenceSource child.inferred.id →
          TemplateScopeCovered evidenceSource context
              (.expression child.inferred.id) →
            ExpressionTypingBase (child.final.toTypedSource roots)
              semanticSource context substitution child.inferred

/-- Attachment retains the old requirements of every argument whenever the
attachment row is known to carry exactly the source-ordered argument ids.
Unlike `argumentRequirementsRetainedAt_attachExpressionCoercions`, this
operational adapter does not require semantic coercion validity first; that
validity is itself proved later from the recursive argument bases. -/
theorem argumentRequirementsRetainedAt_attachExpressionCoercions_of_ids
    {state : Frontend.SourceInference.State}
    {roots : List NodeId} {evidenceSource : TypedSource}
    {substitution : TypeSystem.Substitution}
    {arguments : List InferredExpression}
    {entries : List Detail.ExpressionCoercions}
    (expressionIds : entries.map (·.expression) = arguments.map (·.id))
    (argumentIdsUnique : (arguments.map (·.id)).Nodup)
    (preserved : ExpressionNodesPreservedAt (arguments.map (·.id))
      ((Detail.attachExpressionCoercions state entries
        |>.toTypedSource roots).applySubstitution substitution)
      evidenceSource) :
    ∀ argument ∈ arguments,
      ExpressionRequirementsRetainedAt (state.toTypedSource roots)
        evidenceSource argument.id := by
  intro argument argumentMember
  have argumentIdMember : argument.id ∈ arguments.map (·.id) :=
    List.mem_map.mpr ⟨argument, argumentMember, rfl⟩
  have entryIdMember : argument.id ∈ entries.map (·.expression) := by
    rw [expressionIds]
    exact argumentIdMember
  obtain ⟨entry, entryMember, entryIdEq⟩ := List.mem_map.mp entryIdMember
  have entriesUnique : (entries.map (·.expression)).Nodup := by
    rw [expressionIds]
    exact argumentIdsUnique
  have entryPreserved : ExpressionNodesPreservedAt [entry.expression]
      ((Detail.attachExpressionCoercions state entries
        |>.toTypedSource roots).applySubstitution substitution)
      evidenceSource := by
    intro id node idMember contains
    have idEq : id = entry.expression := by simpa using idMember
    subst id
    apply preserved
    · rw [entryIdEq]
      exact argumentIdMember
    · exact contains
  have retained : ExpressionRequirementsRetainedAt (state.toTypedSource roots)
      evidenceSource entry.expression :=
    ExpressionRequirementsRetainedAt.ofAttachExpressionCoercions
      entriesUnique entryMember entryPreserved
  rw [entryIdEq] at retained
  intro node requirement contains requirementMember
  exact retained contains requirementMember

/-- A source-ordered argument traversal produces pre-attachment bases when
each argument occurrence is known to retain its owned requirements in the
eventual evidence source.  This is the selected-call analogue of
`inferExprsFuel_success_argumentTypingBasesValid_under_ambient_bounded`:
the child-to-argument-state source links remain append-only, while the final
argument roots themselves may be rewritten by coercion attachment. -/
theorem
    inferExprsFuel_success_argumentTypingBasesValid_under_retained_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {expressions : List Syntax.Expr}
    {initial final evidenceState : Frontend.SourceInference.State}
    {inferred : List InferredExpression}
    {semanticSource evidenceSource : TypedSource}
    {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution}
    (roots : List NodeId := [])
    (fuel_lt : fuel < parentFuel)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (integerPatternsSubset :
      final.integerPatterns ⊆ evidenceState.integerPatterns)
    (integerLiteralsSubset :
      final.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirementsSubset : final.requirements ⊆ evidenceState.requirements)
    (retained : ∀ argument ∈ inferred,
      ExpressionRequirementsRetainedAt (final.toTypedSource roots)
        evidenceSource argument.id)
    (childSound : RetainedExpressionChildTypingCallback parentFuel
      inferenceContext (final.toTypedSource roots) semanticSource
      evidenceSource evidenceState target outer roots)
    (success : Detail.inferExprsFuel fuel inferenceContext expressions initial =
      .ok (inferred, final)) :
    ArgumentTypingBasesValid (final.toTypedSource roots) semanticSource target
      outer inferred := by
  induction fuel generalizing expressions initial inferred final with
  | zero =>
      simp [Detail.inferExprsFuel] at success
  | succ fuel induction =>
      cases expressions with
      | nil =>
          simp only [Detail.inferExprsFuel, Except.ok.injEq,
            Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          exact .nil
      | cons expression rest =>
          unfold Detail.inferExprsFuel at success
          cases headSuccess : Detail.inferExprFuel fuel inferenceContext
              expression none initial with
          | error error =>
              simp [headSuccess, bind, Except.bind] at success
          | ok headPair =>
              rcases headPair with ⟨head, headState⟩
              simp only [headSuccess, bind, Except.bind] at success
              cases tailSuccess : Detail.inferExprsFuel fuel inferenceContext
                  rest headState with
              | error error =>
                  simp [tailSuccess] at success
              | ok tailPair =>
                  rcases tailPair with ⟨tail, tailState⟩
                  simp only [tailSuccess, pure, Pure.pure, Except.pure]
                    at success
                  injection success with resultEq
                  cases resultEq
                  have headBelow : headState.NodesBelowNextOccurrence :=
                    (Detail.inferExprFuel_occurrenceBoundExtends headSuccess
                      ).nodesBelowNextOccurrence initialBelow
                  have headToFinal : TypingSourceExtends
                      (headState.toTypedSource roots)
                      (final.toTypedSource roots) :=
                    inferExprsFuel_success_typingSourceExtends_under_bound
                      tailSuccess headBelow roots
                  have headIntegerLiteralsSubset :
                      headState.integerLiterals ⊆
                        evidenceState.integerLiterals :=
                    List.Subset.trans
                      (Detail.inferExprsFuel_integerLiterals_subset tailSuccess)
                      integerLiteralsSubset
                  have headIntegerPatternsSubset :
                      headState.integerPatterns ⊆
                        evidenceState.integerPatterns :=
                    List.Subset.trans
                      (Detail.inferExprsFuel_integerPatterns_subset tailSuccess)
                      integerPatternsSubset
                  have headRequirementsSubset :
                      headState.requirements ⊆ evidenceState.requirements :=
                    List.Subset.trans
                      (Detail.inferExprsFuel_requirements_subset tailSuccess)
                      requirementsSubset
                  let child : ExpressionChildInferenceProvenance parentFuel
                      inferenceContext (final.toTypedSource roots)
                      evidenceState roots := {
                    fuel
                    expression
                    expected := none
                    initial
                    final := headState
                    inferred := head
                    fuel_lt := Nat.lt_trans (Nat.lt_succ_self fuel) fuel_lt
                    initialNodesBelow := initialBelow
                    success := headSuccess
                    sourceExtension := headToFinal
                    integerPatternsSubset := headIntegerPatternsSubset
                    integerLiteralsSubset := headIntegerLiteralsSubset
                    requirementsSubset := headRequirementsSubset
                  }
                  have headRetainedAtFinal : ExpressionRequirementsRetainedAt
                      (final.toTypedSource roots) evidenceSource head.id :=
                    retained head (by simp)
                  have headRetained : ExpressionRequirementsRetainedAt
                      (headState.toTypedSource roots) evidenceSource head.id :=
                    ExpressionRequirementsRetainedAt.monoBefore headToFinal
                      headRetainedAtFinal
                  have headBase := childSound child headRetained
                  have finalHead : ExpressionTypingBase
                      (final.toTypedSource roots) semanticSource target outer
                      head :=
                    headBase.weakenNodeSource headToFinal.nodes_prefix
                  have tailBases := induction
                    (fuel_lt := Nat.lt_trans (Nat.lt_succ_self fuel) fuel_lt)
                    (initialBelow := headBelow)
                    (integerPatternsSubset := integerPatternsSubset)
                    (integerLiteralsSubset := integerLiteralsSubset)
                    (requirementsSubset := requirementsSubset)
                    (retained := by
                      intro argument member
                      exact retained argument (by simp [member]))
                    (childSound := childSound)
                    tailSuccess
                  exact .cons finalHead tailBases

/-- Coverage-aware form of the retained argument sequencer.  Membership in
the successful traversal supplies both the argument's eventual retention and
its scope coverage before the recursive callback is invoked. -/
theorem
    inferExprsFuel_success_argumentTypingBasesValid_under_covered_retained_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {expressions : List Syntax.Expr}
    {initial final evidenceState : Frontend.SourceInference.State}
    {inferred : List InferredExpression}
    {semanticSource evidenceSource : TypedSource}
    {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution}
    (roots : List NodeId := [])
    (fuel_lt : fuel < parentFuel)
    (initialReady : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (initialBelow : initial.NodesBelowNextOccurrence)
    (initialInvariant : ActiveLocalContextInvariant initial outer target)
    (initialBindersBelow : initial.LocalBindersBelowNextLocal)
    (integerPatternsSubset :
      final.integerPatterns ⊆ evidenceState.integerPatterns)
    (integerLiteralsSubset :
      final.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirementsSubset : final.requirements ⊆ evidenceState.requirements)
    (retained : ∀ argument ∈ inferred,
      ExpressionRequirementsRetainedAt (final.toTypedSource roots)
        evidenceSource argument.id)
    (childrenRetained : ∀ argument ∈ inferred,
      ExpressionDirectChildrenRetainedAt (final.toTypedSource roots)
        evidenceSource argument.id)
    (covered : ∀ argument ∈ inferred,
      TemplateScopeCovered evidenceSource target (.expression argument.id))
    (childSound : CoveredRetainedExpressionChildTypingCallback parentFuel
      inferenceContext (final.toTypedSource roots) semanticSource
      evidenceSource evidenceState target outer roots)
    (success : Detail.inferExprsFuel fuel inferenceContext expressions initial =
      .ok (inferred, final)) :
    ArgumentTypingBasesValid (final.toTypedSource roots) semanticSource target
      outer inferred := by
  induction fuel generalizing expressions initial inferred final with
  | zero =>
      simp [Detail.inferExprsFuel] at success
  | succ fuel induction =>
      cases expressions with
      | nil =>
          simp only [Detail.inferExprsFuel, Except.ok.injEq,
            Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          exact .nil
      | cons expression rest =>
          unfold Detail.inferExprsFuel at success
          cases headSuccess : Detail.inferExprFuel fuel inferenceContext
              expression none initial with
          | error error =>
              simp [headSuccess, bind, Except.bind] at success
          | ok headPair =>
              rcases headPair with ⟨head, headState⟩
              simp only [headSuccess, bind, Except.bind] at success
              cases tailSuccess : Detail.inferExprsFuel fuel inferenceContext
                  rest headState with
              | error error =>
                  simp [tailSuccess] at success
              | ok tailPair =>
                  rcases tailPair with ⟨tail, tailState⟩
                  simp only [tailSuccess, pure, Pure.pure, Except.pure]
                    at success
                  injection success with resultEq
                  cases resultEq
                  have headBelow : headState.NodesBelowNextOccurrence :=
                    (Detail.inferExprFuel_occurrenceBoundExtends headSuccess
                      ).nodesBelowNextOccurrence initialBelow
                  have headToFinal : TypingSourceExtends
                      (headState.toTypedSource roots)
                      (final.toTypedSource roots) :=
                    inferExprsFuel_success_typingSourceExtends_under_bound
                      tailSuccess headBelow roots
                  have headIntegerLiteralsSubset :
                      headState.integerLiterals ⊆
                        evidenceState.integerLiterals :=
                    List.Subset.trans
                      (Detail.inferExprsFuel_integerLiterals_subset tailSuccess)
                      integerLiteralsSubset
                  have headIntegerPatternsSubset :
                      headState.integerPatterns ⊆
                        evidenceState.integerPatterns :=
                    List.Subset.trans
                      (Detail.inferExprsFuel_integerPatterns_subset tailSuccess)
                      integerPatternsSubset
                  have headRequirementsSubset :
                      headState.requirements ⊆ evidenceState.requirements :=
                    List.Subset.trans
                      (Detail.inferExprsFuel_requirements_subset tailSuccess)
                      requirementsSubset
                  let child : ExpressionChildInferenceProvenance parentFuel
                      inferenceContext (final.toTypedSource roots)
                      evidenceState roots := {
                    fuel
                    expression
                    expected := none
                    initial
                    final := headState
                    inferred := head
                    fuel_lt := Nat.lt_trans (Nat.lt_succ_self fuel) fuel_lt
                    initialNodesBelow := initialBelow
                    success := headSuccess
                    sourceExtension := headToFinal
                    integerPatternsSubset := headIntegerPatternsSubset
                    integerLiteralsSubset := headIntegerLiteralsSubset
                    requirementsSubset := headRequirementsSubset
                  }
                  have headRetainedAtFinal : ExpressionRequirementsRetainedAt
                      (final.toTypedSource roots) evidenceSource head.id :=
                    retained head (by simp)
                  have headRetained : ExpressionRequirementsRetainedAt
                      (headState.toTypedSource roots) evidenceSource head.id :=
                    ExpressionRequirementsRetainedAt.monoBefore headToFinal
                      headRetainedAtFinal
                  have headProperties := Detail.inferExprFuel_inferenceProperties
                    initialReady signatureFormation functionsCanonical (by
                      intro expectedType member
                      simp at member) headSuccess
                  have headInvariant : ActiveLocalContextInvariant headState
                      outer target :=
                    initialInvariant.inferExprFuel headSuccess
                  have headBindersBelow :
                      headState.LocalBindersBelowNextLocal :=
                    Detail.inferExprFuel_preserves_localBindersBelowNextLocal
                      initialBindersBelow headSuccess
                  have headChildrenRetainedAtFinal :
                      ExpressionDirectChildrenRetainedAt
                        (final.toTypedSource roots) evidenceSource head.id :=
                    childrenRetained head (by simp)
                  have headChildrenRetained :
                      ExpressionDirectChildrenRetainedAt
                        (headState.toTypedSource roots) evidenceSource
                        head.id :=
                    ExpressionDirectChildrenRetainedAt.monoBefore headToFinal
                      headChildrenRetainedAtFinal
                  have headCovered : TemplateScopeCovered evidenceSource
                      target (.expression head.id) :=
                    covered head (by simp)
                  have headBase := childSound child initialReady (by
                      intro expectedType member
                      simp at member)
                    initialInvariant initialBindersBelow headRetained
                    headChildrenRetained headCovered
                  have finalHead : ExpressionTypingBase
                      (final.toTypedSource roots) semanticSource target outer
                      head :=
                    headBase.weakenNodeSource headToFinal.nodes_prefix
                  have tailBases := induction
                    (fuel_lt := Nat.lt_trans (Nat.lt_succ_self fuel) fuel_lt)
                    (initialReady := headProperties.2.1)
                    (initialBelow := headBelow)
                    (initialInvariant := headInvariant)
                    (initialBindersBelow := headBindersBelow)
                    (integerPatternsSubset := integerPatternsSubset)
                    (integerLiteralsSubset := integerLiteralsSubset)
                    (requirementsSubset := requirementsSubset)
                    (retained := by
                      intro argument member
                      exact retained argument (by simp [member]))
                    (childrenRetained := by
                      intro argument member
                      exact childrenRetained argument (by simp [member]))
                    (covered := by
                      intro argument member
                      exact covered argument (by simp [member]))
                    (childSound := childSound)
                    tailSuccess
                  exact .cons finalHead tailBases

/-- Selected-call soundness with one whole-body, retention-aware recursive
boundary.  Candidate search does not allocate occurrences, so the actual
argument traversal remains the node source for recursive bases.  Delayed
argument coercions are handled only through scoped preservation and
requirement retention; no false append-only extension across attachment is
assumed. -/
theorem
    inferExprsFuel_selectFunctionCandidateFrom_recordSelectedCall_success_expressionTypingBase_under_scoped_retention_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {argumentSources : List Syntax.Expr}
    {argumentInitial argumentState evidenceState :
      Frontend.SourceInference.State}
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
    {semanticSource evidenceSource : TypedSource}
    {closedVariables : List TypeSystem.TypeVarId}
    (fuel_lt : fuel < parentFuel)
    (argumentsSuccess : Detail.inferExprsFuel fuel inferenceContext
      argumentSources argumentInitial = .ok (arguments, argumentState))
    (selectionSuccess : Detail.selectFunctionCandidateFrom inferenceContext
      name candidates arguments integerLiteralOrigins call expected
      argumentState = .ok attempt)
    (recordEq : Detail.recordSelectedCall source callee name arguments attempt =
      (result, resultState))
    (candidatesSubset : candidates ⊆ inferenceContext.signatures.functions)
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
    (argumentIntegerPatternsSubset :
      argumentState.integerPatterns ⊆ evidenceState.integerPatterns)
    (argumentIntegerSubset :
      argumentState.integerLiterals ⊆ evidenceState.integerLiterals)
    (argumentRequirementsSubset :
      argumentState.requirements ⊆ evidenceState.requirements)
    (childSound : RetainedExpressionChildTypingCallback parentFuel
      inferenceContext (argumentState.toTypedSource roots) semanticSource
      evidenceSource evidenceState active later.inference.substitution roots)
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
    (argumentCovered : ∀ entry ∈ attempt.argumentCoercions,
      TemplateScopeCovered evidenceSource active
        (.expression entry.expression))
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
  have argumentProperties := Detail.inferExprsFuel_inferenceProperties
    argumentInitialReady signatureFormation functionsCanonical argumentsSuccess
  have expectedAtArguments : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow argumentState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      argumentProperties.1.next_le
  have argumentIdsUnique :=
    Detail.inferExprsFuel_success_ids_nodup argumentsSuccess
  obtain ⟨signature, _, _, canonical, _, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_semanticCandidate signatureFormation
      functionsCanonical signaturesEq candidatesSubset selectionSuccess
  have argumentExpressionIds :
      attempt.argumentCoercions.map (·.expression) =
        arguments.map (·.id) :=
    Detail.tryFunctionCandidate_some_argumentCoercion_expression_ids
      canonical candidateSuccess
  have retainedAtAttempt :=
    argumentRequirementsRetainedAt_attachExpressionCoercions_of_ids
      argumentExpressionIds argumentIdsUnique evidenceArgumentNodesPreserved
  have candidateNodesEq : attempt.state.nodes = argumentState.nodes :=
    (Detail.tryFunctionCandidate_some_occurrenceState_eq candidateSuccess).1
  have retainedAtArguments : ∀ argument ∈ arguments,
      ExpressionRequirementsRetainedAt
        (argumentState.toTypedSource roots) evidenceSource argument.id := by
    intro argument argumentMember node requirement contains requirementMember
    apply retainedAtAttempt argument argumentMember
    · rcases contains with ⟨member, idEq⟩
      refine ⟨?_, idEq⟩
      change Node.expression node ∈ attempt.state.nodes
      rw [candidateNodesEq]
      exact member
    · exact requirementMember
  have bases :=
    inferExprsFuel_success_argumentTypingBasesValid_under_retained_bounded
      (roots := roots) fuel_lt nodesBelow argumentIntegerPatternsSubset
      argumentIntegerSubset argumentRequirementsSubset retainedAtArguments
      childSound argumentsSuccess
  exact
    selectFunctionCandidateFrom_recordSelectedCall_success_expressionTypingBase_scoped_of_retained
      selectionSuccess recordEq candidatesSubset bases argumentIdsUnique
      argumentProperties.2.1 argumentProperties.2.2 signatureFormation
      functionsCanonical expectedAtArguments substitutionExtends
      requirementsSubset semanticArgumentNodesPreserved
      semanticCalleeNodePreserved evidenceArgumentNodesPreserved
      callRequirementsRetained argumentCovered catalog binders residual
      contextValid signaturesEq traitSuccess profileSuccess traitName
      solveSuccess solvedEq ledger ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono callCovered

/-- Coverage-aware selected-call bridge used by the eventual closed mutual
fuel induction.  The selected attachment row identifies exactly the inferred
arguments, so its certified argument coverage is converted pointwise into the
coverage demanded by the recursive callback. -/
theorem
    inferExprsFuel_selectFunctionCandidateFrom_recordSelectedCall_success_expressionTypingBase_under_covered_scoped_retention_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {argumentSources : List Syntax.Expr}
    {argumentInitial argumentState evidenceState :
      Frontend.SourceInference.State}
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
    {semanticSource evidenceSource : TypedSource}
    {closedVariables : List TypeSystem.TypeVarId}
    (fuel_lt : fuel < parentFuel)
    (argumentsSuccess : Detail.inferExprsFuel fuel inferenceContext
      argumentSources argumentInitial = .ok (arguments, argumentState))
    (selectionSuccess : Detail.selectFunctionCandidateFrom inferenceContext
      name candidates arguments integerLiteralOrigins call expected
      argumentState = .ok attempt)
    (recordEq : Detail.recordSelectedCall source callee name arguments attempt =
      (result, resultState))
    (candidatesSubset : candidates ⊆ inferenceContext.signatures.functions)
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
    (argumentInitialInvariant : ActiveLocalContextInvariant argumentInitial
      later.inference.substitution active)
    (argumentInitialBindersBelow :
      argumentInitial.LocalBindersBelowNextLocal)
    (argumentIntegerPatternsSubset :
      argumentState.integerPatterns ⊆ evidenceState.integerPatterns)
    (argumentIntegerSubset :
      argumentState.integerLiterals ⊆ evidenceState.integerLiterals)
    (argumentRequirementsSubset :
      argumentState.requirements ⊆ evidenceState.requirements)
    (childSound : CoveredRetainedExpressionChildTypingCallback parentFuel
      inferenceContext (argumentState.toTypedSource roots) semanticSource
      evidenceSource evidenceState active later.inference.substitution roots)
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
    (argumentCovered : ∀ entry ∈ attempt.argumentCoercions,
      TemplateScopeCovered evidenceSource active
        (.expression entry.expression))
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
  have argumentProperties := Detail.inferExprsFuel_inferenceProperties
    argumentInitialReady signatureFormation functionsCanonical argumentsSuccess
  have expectedAtArguments : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow argumentState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      argumentProperties.1.next_le
  have argumentIdsUnique :=
    Detail.inferExprsFuel_success_ids_nodup argumentsSuccess
  obtain ⟨signature, _, _, canonical, _, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_semanticCandidate signatureFormation
      functionsCanonical signaturesEq candidatesSubset selectionSuccess
  have argumentExpressionIds :
      attempt.argumentCoercions.map (·.expression) =
        arguments.map (·.id) :=
    Detail.tryFunctionCandidate_some_argumentCoercion_expression_ids
      canonical candidateSuccess
  have retainedAtAttempt :=
    argumentRequirementsRetainedAt_attachExpressionCoercions_of_ids
      argumentExpressionIds argumentIdsUnique evidenceArgumentNodesPreserved
  have candidateNodesEq : attempt.state.nodes = argumentState.nodes :=
    (Detail.tryFunctionCandidate_some_occurrenceState_eq candidateSuccess).1
  have retainedAtArguments : ∀ argument ∈ arguments,
      ExpressionRequirementsRetainedAt
        (argumentState.toTypedSource roots) evidenceSource argument.id := by
    intro argument argumentMember node requirement contains requirementMember
    apply retainedAtAttempt argument argumentMember
    · rcases contains with ⟨member, idEq⟩
      refine ⟨?_, idEq⟩
      change Node.expression node ∈ attempt.state.nodes
      rw [candidateNodesEq]
      exact member
    · exact requirementMember
  have childrenRetainedAtArguments : ∀ argument ∈ arguments,
      ExpressionDirectChildrenRetainedAt
        (argumentState.toTypedSource roots) evidenceSource argument.id := by
    intro argument argumentMember
    have argumentToAttempt : ExpressionDirectChildrenRetainedAt
        (argumentState.toTypedSource roots) (attempt.state.toTypedSource roots)
        argument.id := by
      apply ExpressionDirectChildrenRetainedAt.ofNodesEq
      exact candidateNodesEq
    have attemptToAttached : ExpressionDirectChildrenRetainedAt
        (attempt.state.toTypedSource roots)
        ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions).toTypedSource roots) argument.id :=
      ExpressionDirectChildrenRetainedAt.ofAttachExpressionCoercions
        attempt.state attempt.argumentCoercions roots argument.id
    have attachedToEvidence : ExpressionDirectChildrenRetainedAt
        ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions).toTypedSource roots)
        evidenceSource argument.id := by
      apply ExpressionDirectChildrenRetainedAt.ofExpressionNodesPreservedAt
        (substitution := later.inference.substitution)
      intro id node idMember contains
      simp only [List.mem_singleton] at idMember
      subst id
      apply evidenceArgumentNodesPreserved
      · exact List.mem_map.mpr ⟨argument, argumentMember, rfl⟩
      · exact contains
    intro child edge
    exact attachedToEvidence (attemptToAttached (argumentToAttempt edge))
  have coveredArguments : ∀ argument ∈ arguments,
      TemplateScopeCovered evidenceSource active
        (.expression argument.id) := by
    intro argument argumentMember
    have argumentIdMember : argument.id ∈ arguments.map (·.id) :=
      List.mem_map.mpr ⟨argument, argumentMember, rfl⟩
    have entryIdMember : argument.id ∈
        attempt.argumentCoercions.map (·.expression) := by
      rw [argumentExpressionIds]
      exact argumentIdMember
    obtain ⟨entry, entryMember, entryIdEq⟩ :=
      List.mem_map.mp entryIdMember
    simpa only [entryIdEq] using argumentCovered entry entryMember
  have bases :=
    inferExprsFuel_success_argumentTypingBasesValid_under_covered_retained_bounded
      (roots := roots) fuel_lt argumentInitialReady signatureFormation
      functionsCanonical nodesBelow argumentInitialInvariant
      argumentInitialBindersBelow argumentIntegerPatternsSubset
      argumentIntegerSubset argumentRequirementsSubset retainedAtArguments
      childrenRetainedAtArguments coveredArguments childSound argumentsSuccess
  exact
    selectFunctionCandidateFrom_recordSelectedCall_success_expressionTypingBase_scoped_of_retained
      selectionSuccess recordEq candidatesSubset bases argumentIdsUnique
      argumentProperties.2.1 argumentProperties.2.2 signatureFormation
      functionsCanonical expectedAtArguments substitutionExtends
      requirementsSubset semanticArgumentNodesPreserved
      semanticCalleeNodePreserved evidenceArgumentNodesPreserved
      callRequirementsRetained argumentCovered catalog binders residual
      contextValid signaturesEq traitSuccess profileSuccess traitName
      solveSuccess solvedEq ledger ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono callCovered

/-- The four successful executable tails of a source call.  Constructor
discovery precedes ordinary call dispatch; a non-constructor call first
traverses its argument row and then records either a selected direct call, a
builtin call, or an indirect call through a recursively inferred callee. -/
inductive CallExpressionDispatchFacts
    (context : Frontend.SourceInference.Context)
    (source callee : Syntax.Expr)
    (arguments : Syntax.DelimitedList Syntax.Expr)
    (id : ExpressionId) (expected : Option TypeSystem.Ty)
    (fuel : Nat) (allocated : Frontend.SourceInference.State)
    (result : InferredExpression × Frontend.SourceInference.State) : Prop where
  | constructor
      {dataType : ProgramDataSignature}
      {constructor : ProgramDataConstructorSignature}
      {instantiation : DataConstructorInstantiation}
      {constructorState : Frontend.SourceInference.State}
      (discovery : Detail.constructorCalleeCandidates context allocated callee =
        .ok [(dataType, constructor)])
      (freshInstantiation :
        Detail.freshDataConstructorInstantiation dataType constructor allocated =
          (instantiation, constructorState))
      (application : Detail.inferConstructorApplicationFuel fuel context source
        id instantiation arguments.elements expected constructorState =
          .ok result) :
      CallExpressionDispatchFacts context source callee arguments id expected
        fuel allocated result
  | selected
      {inferredArguments : List InferredExpression}
      {argumentState : Frontend.SourceInference.State}
      {name : String} {candidates : List ProgramFunctionSignature}
      {integerLiterals : List IntegerLiteralOrigin}
      {attempt : Detail.CandidateAttemptResult}
      (argumentsSuccess : Detail.inferExprsFuel fuel context arguments.elements
        allocated = .ok (inferredArguments, argumentState))
      (candidateOrigin :
        SelectedCallCandidatesOrigin context name candidates)
      (selection : Detail.selectFunctionCandidateFrom context name candidates
        inferredArguments integerLiterals id expected argumentState =
          .ok attempt)
      (recording : Detail.recordSelectedCall source callee name
        inferredArguments attempt = result) :
      CallExpressionDispatchFacts context source callee arguments id expected
        fuel allocated result
  | builtin
      {inferredArguments : List InferredExpression}
      {argumentState : Frontend.SourceInference.State}
      {name : String} {function : BuiltinFunctionId}
      (argumentsSuccess : Detail.inferExprsFuel fuel context arguments.elements
        allocated = .ok (inferredArguments, argumentState))
      (recording : Detail.recordBuiltinFunctionCall source callee name function
        inferredArguments id expected argumentState = .ok result) :
      CallExpressionDispatchFacts context source callee arguments id expected
        fuel allocated result
  | indirect
      {inferredArguments : List InferredExpression}
      {argumentState calleeState : Frontend.SourceInference.State}
      {inferredCallee : InferredExpression}
      {application : Detail.IndirectApplicationResult}
      (argumentsSuccess : Detail.inferExprsFuel fuel context arguments.elements
        allocated = .ok (inferredArguments, argumentState))
      (calleeSuccess : Detail.inferExprFuel fuel context callee none
        argumentState = .ok (inferredCallee, calleeState))
      (applicationSuccess : Detail.applyFunctionType context id
        inferredCallee.type inferredArguments expected calleeState =
          .ok application)
      (recording : Detail.recordIndirectCall source inferredCallee
        inferredArguments application = result) :
      CallExpressionDispatchFacts context source callee arguments id expected
        fuel allocated result

/-- Invert a successful source call into the exact semantic tail executed by
the frontend. -/
theorem inferExprFuel_success_call_dispatch_facts
    {fuel : Nat}
    {context : Frontend.SourceInference.Context}
    {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr}
    {expected : Option TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId}
    {result : InferredExpression × Frontend.SourceInference.State}
    (expressionEq : source.value = .call callee arguments)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) context source expected initial =
      .ok result) :
    CallExpressionDispatchFacts context source callee arguments id expected
      fuel allocated result := by
  unfold Detail.inferExprFuel at success
  simp only [allocationEq, expressionEq, bind, Except.bind] at success
  cases discovery : Detail.constructorCalleeCandidates context allocated callee with
  | error error =>
      simp [discovery] at success
  | ok candidates =>
      cases candidates with
      | nil =>
          simp only [discovery] at success
          repeat' first | split at success
          all_goals
            try simp_all [pure, Pure.pure, Except.pure]
          all_goals
            first
            | apply CallExpressionDispatchFacts.indirect <;> assumption
            | apply CallExpressionDispatchFacts.builtin <;> assumption
            | apply CallExpressionDispatchFacts.selected
              · assumption
              · first
                | apply SelectedCallCandidatesOrigin.qualified <;> assumption
                | apply SelectedCallCandidatesOrigin.unqualified <;> assumption
              · assumption
              · assumption
      | cons first rest =>
          rcases first with ⟨dataType, constructor⟩
          cases rest with
          | nil =>
              simp only [discovery] at success
              generalize freshEq :
                Detail.freshDataConstructorInstantiation dataType constructor
                  allocated = pair at success
              rcases pair with ⟨instantiation, constructorState⟩
              exact .constructor discovery freshEq success
          | cons second tail =>
              simp [discovery] at success

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceExpressionOperatorSoundness
/-!
Bounded expression-typing bridges for operator operands.  Selected named
operators attach argument coercions to already recorded operand nodes, so
their recursive boundary uses requirement retention rather than a false
whole-node-table prefix claim.  Ordinary and trait operators retain the
existing prefix-based child boundary.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend SourceInference TypeSystem

private theorem operatorRecord_nodesPrefix
    {inferenceContext : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm}
    {requirements : List RequirementId}
    {expected : Option Ty}
    {initial : Frontend.SourceInference.State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × Frontend.SourceInference.State}
    (success : Detail.recordExpressionWithExpected inferenceContext source id
      type form requirements expected initial localSchemeInstantiationStart =
        .ok result) :
    initial.nodes <+: result.2.nodes := by
  obtain ⟨fitted, fittedSuccess, _, resultStateEq⟩ :=
    Detail.recordExpressionWithExpected_success_record success
  have fittedPrefix : initial.nodes <+: fitted.state.nodes := by
    rw [(Detail.withExpected_occurrenceState_eq fittedSuccess).1]
    exact List.prefix_rfl
  rw [resultStateEq]
  exact fittedPrefix.trans
    (Frontend.SourceInference.State.recordNode_nodesPrefix fitted.state _)

/-- For an ordinary or trait unary operator, the actual operand is an
append-only recursive child of the enclosing expression.  Selected named
operators use the separate retention-aware boundary below. -/
def ordinaryUnary_childProvenance
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {expression operand : Syntax.Expr}
    {operator : Syntax.Located Syntax.UnaryOp}
    {expected : Option Ty}
    {initial allocated operandState evidenceState :
      Frontend.SourceInference.State}
    {id : ExpressionId} {operandResult : InferredExpression}
    {inferred : Detail.OperatorInferenceResult}
    {result : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {integerLiterals : List IntegerLiteralOrigin}
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (parentSuccess : Detail.inferExprFuel (fuel + 1) inferenceContext
      expression expected initial = .ok result)
    (operandSuccess : Detail.inferExprFuel fuel inferenceContext operand none
      allocated = .ok (operandResult, operandState))
    (operatorSuccess : Detail.inferUnaryOperator inferenceContext
      operator.value operandResult.type expected integerLiterals operandState =
        .ok inferred)
    (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
      expression id inferred.type (.unary operator.value operandResult.id)
      inferred.requirements expected inferred.state = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (parentExtension : TypingSourceExtends
      (result.2.toTypedSource roots) (evidenceState.toTypedSource roots))
    (operandIntegerSubset :
      operandState.integerLiterals ⊆ result.2.integerLiterals)
    (parentIntegerSubset :
      result.2.integerLiterals ⊆ evidenceState.integerLiterals)
    (operandPatternSubset :
      operandState.integerPatterns ⊆ result.2.integerPatterns)
    (parentPatternSubset :
      result.2.integerPatterns ⊆ evidenceState.integerPatterns)
    (parentRequirementsSubset :
      result.2.requirements ⊆ evidenceState.requirements) :
    ExpressionChildInferenceProvenance (fuel + 1) inferenceContext
      (evidenceState.toTypedSource roots) evidenceState roots := by
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have below :=
      State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial
        initialBelow
    have allocatedEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [allocatedEq] using below
  have allocatedOwner : allocated.owner = initial.owner := by
    have allocatedEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← allocatedEq]
    rfl
  have operandOwner : operandState.owner = allocated.owner :=
    Detail.inferExprFuel_preserves_owner operandSuccess
  have parentOwner : result.2.owner = initial.owner :=
    Detail.inferExprFuel_preserves_owner parentSuccess
  have operandToParent : TypingSourceExtends
      (operandState.toTypedSource roots) (result.2.toTypedSource roots) := by
    constructor
    · exact parentOwner.trans (allocatedOwner.symm.trans operandOwner.symm)
    · have operatorNodes :=
        (Detail.inferUnaryOperator_occurrenceState_eq operatorSuccess).1
      change operandState.nodes <+: result.2.nodes
      rw [← operatorNodes]
      exact operatorRecord_nodesPrefix recordSuccess
  have operandRequirementsSubset : operandState.requirements ⊆
      evidenceState.requirements :=
    List.Subset.trans
      (List.Subset.trans
        (Detail.inferUnaryOperator_requirements_subset operatorSuccess)
        (Detail.recordExpressionWithExpected_requirements_subset
          recordSuccess)) parentRequirementsSubset
  exact {
    fuel
    expression := operand
    expected := none
    initial := allocated
    final := operandState
    inferred := operandResult
    fuel_lt := Nat.lt_succ_self fuel
    initialNodesBelow := allocatedBelow
    success := operandSuccess
    sourceExtension := TypingSourceExtends.trans operandToParent
      parentExtension
    integerLiteralsSubset := List.Subset.trans operandIntegerSubset
      parentIntegerSubset
    integerPatternsSubset := List.Subset.trans operandPatternSubset
      parentPatternSubset
    requirementsSubset := operandRequirementsSubset
  }

/-- In a recorded binary operator, both actual operand traces are append-only
children of the parent result.  The left source first extends through the
right traversal; the operator inference and recording tail then preserve the
completed right node table. -/
def ordinaryBinary_childProvenances
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {expression left right : Syntax.Expr}
    {operator : Syntax.Located Syntax.BinaryOp}
    {expected : Option Ty}
    {initial allocated leftState rightState evidenceState :
      Frontend.SourceInference.State}
    {id : ExpressionId}
    {leftResult rightResult : InferredExpression}
    {inferred : Detail.OperatorInferenceResult}
    {result : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {integerLiterals : List IntegerLiteralOrigin}
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (parentSuccess : Detail.inferExprFuel (fuel + 1) inferenceContext
      expression expected initial = .ok result)
    (leftSuccess : Detail.inferExprFuel fuel inferenceContext left none
      allocated = .ok (leftResult, leftState))
    (rightSuccess : Detail.inferExprFuel fuel inferenceContext right none
      leftState = .ok (rightResult, rightState))
    (operatorSuccess : Detail.inferBinaryOperator inferenceContext
      operator.value leftResult.type rightResult.type expected integerLiterals
      rightState = .ok inferred)
    (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
      expression id inferred.type
      (.binary leftResult.id operator.value rightResult.id)
      inferred.requirements expected inferred.state = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (parentExtension : TypingSourceExtends
      (result.2.toTypedSource roots) (evidenceState.toTypedSource roots))
    (rightIntegerSubset :
      rightState.integerLiterals ⊆ result.2.integerLiterals)
    (parentIntegerSubset :
      result.2.integerLiterals ⊆ evidenceState.integerLiterals)
    (rightPatternSubset :
      rightState.integerPatterns ⊆ result.2.integerPatterns)
    (parentPatternSubset :
      result.2.integerPatterns ⊆ evidenceState.integerPatterns)
    (parentRequirementsSubset :
      result.2.requirements ⊆ evidenceState.requirements) :
    ExpressionChildInferenceProvenance (fuel + 1) inferenceContext
        (evidenceState.toTypedSource roots) evidenceState roots ×
      ExpressionChildInferenceProvenance (fuel + 1) inferenceContext
        (evidenceState.toTypedSource roots) evidenceState roots := by
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have below :=
      State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial
        initialBelow
    have allocatedEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [allocatedEq] using below
  have leftBelow : leftState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends leftSuccess
      ).nodesBelowNextOccurrence allocatedBelow
  have leftToRight : TypingSourceExtends
      (leftState.toTypedSource roots) (rightState.toTypedSource roots) := by
    constructor
    · exact Detail.inferExprFuel_preserves_owner rightSuccess
    · change leftState.nodes <+: rightState.nodes
      exact Detail.inferExprFuel_preserves_nodesPrefix rightSuccess
        List.prefix_rfl leftBelow (Nat.le_refl _)
  have allocatedOwner : allocated.owner = initial.owner := by
    have allocatedEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← allocatedEq]
    rfl
  have leftOwner : leftState.owner = allocated.owner :=
    Detail.inferExprFuel_preserves_owner leftSuccess
  have rightOwner : rightState.owner = leftState.owner :=
    Detail.inferExprFuel_preserves_owner rightSuccess
  have parentOwner : result.2.owner = initial.owner :=
    Detail.inferExprFuel_preserves_owner parentSuccess
  have rightToParent : TypingSourceExtends
      (rightState.toTypedSource roots) (result.2.toTypedSource roots) := by
    constructor
    · exact parentOwner.trans
        (allocatedOwner.symm.trans (leftOwner.symm.trans rightOwner.symm))
    · have operatorNodes :=
        (Detail.inferBinaryOperator_occurrenceState_eq operatorSuccess).1
      change rightState.nodes <+: result.2.nodes
      rw [← operatorNodes]
      exact operatorRecord_nodesPrefix recordSuccess
  have rightToEvidence : TypingSourceExtends
      (rightState.toTypedSource roots) (evidenceState.toTypedSource roots) :=
    TypingSourceExtends.trans rightToParent parentExtension
  have rightRequirementsSubset : rightState.requirements ⊆
      evidenceState.requirements :=
    List.Subset.trans
      (List.Subset.trans
        (Detail.inferBinaryOperator_requirements_subset operatorSuccess)
        (Detail.recordExpressionWithExpected_requirements_subset
          recordSuccess)) parentRequirementsSubset
  have rightIntegerEvidence : rightState.integerLiterals ⊆
      evidenceState.integerLiterals :=
    List.Subset.trans rightIntegerSubset parentIntegerSubset
  have rightPatternEvidence : rightState.integerPatterns ⊆
      evidenceState.integerPatterns :=
    List.Subset.trans rightPatternSubset parentPatternSubset
  have leftRequirementsSubset : leftState.requirements ⊆
      evidenceState.requirements :=
    List.Subset.trans (Detail.inferExprFuel_requirements_subset rightSuccess)
      rightRequirementsSubset
  have leftIntegerEvidence : leftState.integerLiterals ⊆
      evidenceState.integerLiterals :=
    List.Subset.trans (Detail.inferExprFuel_integerLiterals_subset rightSuccess)
      rightIntegerEvidence
  have leftPatternEvidence : leftState.integerPatterns ⊆
      evidenceState.integerPatterns :=
    List.Subset.trans (Detail.inferExprFuel_integerPatterns_subset rightSuccess)
      rightPatternEvidence
  exact ({
    fuel
    expression := left
    expected := none
    initial := allocated
    final := leftState
    inferred := leftResult
    fuel_lt := Nat.lt_succ_self fuel
    initialNodesBelow := allocatedBelow
    success := leftSuccess
    sourceExtension := TypingSourceExtends.trans leftToRight rightToEvidence
    integerLiteralsSubset := leftIntegerEvidence
    integerPatternsSubset := leftPatternEvidence
    requirementsSubset := leftRequirementsSubset
  }, {
    fuel
    expression := right
    expected := none
    initial := leftState
    final := rightState
    inferred := rightResult
    fuel_lt := Nat.lt_succ_self fuel
    initialNodesBelow := leftBelow
    success := rightSuccess
    sourceExtension := rightToEvidence
    integerLiteralsSubset := rightIntegerEvidence
    integerPatternsSubset := rightPatternEvidence
    requirementsSubset := rightRequirementsSubset
  })

/-- The direct/trait unary recording tail closes against a bounded proof of
its actual operand.  The non-recursive operator certificate supplies the
operator rule; finalization supplies requirement evidence and coercion data. -/
theorem ordinaryUnary_expressionTypingBase_under_ambient_bounded
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : Ty} {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {fuel : Nat} {expression operand : Syntax.Expr}
    {operator : Syntax.Located Syntax.UnaryOp} {expected : Option Ty}
    {initial allocated operandState : Frontend.SourceInference.State}
    {id : ExpressionId} {operandResult : InferredExpression}
    {inferred : Detail.OperatorInferenceResult}
    {result : InferredExpression × Frontend.SourceInference.State}
    {integerLiterals : List IntegerLiteralOrigin}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {sourceContext active : SourceSemantics.Context}
    {closedVariables : List TypeVarId}
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (parentSuccess : Detail.inferExprFuel (fuel + 1) inferenceContext
      expression expected initial = .ok result)
    (operandSuccess : Detail.inferExprFuel fuel inferenceContext operand none
      allocated = .ok (operandResult, operandState))
    (operatorSuccess : Detail.inferUnaryOperator inferenceContext
      operator.value operandResult.type expected integerLiterals operandState =
        .ok inferred)
    (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
      expression id inferred.type (.unary operator.value operandResult.id)
      inferred.requirements expected inferred.state = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (parentExtension : TypingSourceExtends
      (result.2.toTypedSource roots) (evidenceState.toTypedSource roots))
    (operandIntegerSubset :
      operandState.integerLiterals ⊆ result.2.integerLiterals)
    (parentIntegerSubset :
      result.2.integerLiterals ⊆ evidenceState.integerLiterals)
    (operandPatternSubset :
      operandState.integerPatterns ⊆ result.2.integerPatterns)
    (parentPatternSubset :
      result.2.integerPatterns ⊆ evidenceState.integerPatterns)
    (parentRequirementsSubset :
      result.2.requirements ⊆ evidenceState.requirements)
    (childSound : ExpressionChildTypingCallback (fuel + 1)
      inferenceContext (evidenceState.toTypedSource roots)
      finalized.typedSource evidenceState active finalized.substitution roots)
    (operandReady : operandState.InferenceReady)
    (operandBelow : operandResult.type.VariablesBelow
      operandState.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow operandState.inference.next)
    (integerLiteralsSubset :
      integerLiterals ⊆ resources.finalState.integerLiterals)
    (integerLiteralTargetsSupported : ∀ origin,
      origin ∈ resources.finalState.integerLiterals →
        resources.finalState.inference.substitution.apply
          (.variable origin.metavariable) = .word ∨
        resources.finalState.inference.substitution.apply
          (.variable origin.metavariable) = .integer)
    (substitutionExtends : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (activeCatalog : SignatureCatalogWellFormed active.signatures)
    (activeBinders : TypeParameterBindersWellFormed active)
    (sourceBinders : TypeParameterBindersWellFormed sourceContext)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (selectedTraitName : ∀ {selectedTrait : Resolved.DeclarationId}
      {traitName : String},
      Detail.operatorTrait? inferenceContext traitName =
          .ok (some selectedTrait) →
        (inferenceContext.signatures.trait? selectedTrait).map (·.name) =
          some traitName)
    (traitSuccess : Detail.conventionalTraitWithArity? inferenceContext
      "Coerce" 2 = .ok (some trait))
    (profileSuccess : Detail.coercionMethodProfile? inferenceContext trait =
      .ok (some profile))
    (traitName : (inferenceContext.signatures.trait? trait).map (·.name) =
      some "Coerce")
    (activeSignaturesEq : active.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (activeRequirementsEq : active.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    (assumptionsMono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        active.assumptions)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots)
      finalized.typedSource active finalized.substitution result.1 := by
  let child := ordinaryUnary_childProvenance allocationEq parentSuccess
    operandSuccess operatorSuccess recordSuccess initialBelow parentExtension
    operandIntegerSubset parentIntegerSubset operandPatternSubset
    parentPatternSubset parentRequirementsSubset
  have operandType : ExpressionHasType finalized.typedSource active
      operandResult.id (finalized.substitution.apply operandResult.type) :=
    resources.expressionHasType_of_childProvenance childSound child
      sourceBinders signaturesEq parametersEq ownerEq residual contextValid
  have parentToSemantic : TypingSourceExtends
      ((result.2.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource := by
    have evidenceToSemantic : TypingSourceExtends
        ((evidenceState.toTypedSource roots).applySubstitution
          finalized.substitution) finalized.typedSource := by
      rw [resources.source_eq]
      exact .refl _
    exact TypingSourceExtends.trans
      (parentExtension.applySubstitution finalized.substitution)
      evidenceToSemantic
  have retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) finalized.typedSource result.1.id :=
    ExpressionRequirementsRetainedAt.ofTypingSourceExtends
      finalized.substitution parentToSemantic
  have finalRequirementsSubset : result.2.requirements ⊆
      resources.finalState.requirements := by
    rw [resources.requirements_eq]
    exact parentRequirementsSubset
  have finalSubstitutionExtends :
      resources.finalState.inference.substitution.SemanticallyExtends
        result.2.inference.substitution := by
    simpa only [← resources.substitution_eq] using substitutionExtends
  have finalContextValid : FlexibleSubstitution.ContextSubstitutionValid
      resources.finalState.inference.substitution closedVariables
      sourceContext active := by
    simpa only [← resources.substitution_eq] using contextValid
  simpa only [← resources.substitution_eq] using
    (inferUnaryOperator_recordExpressionWithExpected_success_expressionTypingBase_scoped_of_retained
      (later := resources.finalState)
      (base := finalizedRequirementContext inferenceContext finalized)
      operatorSuccess recordSuccess
      (by simpa only [← resources.substitution_eq] using operandType)
      operandReady operandBelow expectedBelow integerLiteralsSubset
      integerLiteralTargetsSupported finalSubstitutionExtends
      finalRequirementsSubset retained activeCatalog activeBinders
      traitSuccess profileSuccess catalog finalContextValid signaturesEq
      selectedTraitName traitName resources.solve_success
      resources.solved_context_eq resources.ledger resources.ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered)

/-- The direct/trait binary recording tail closes both actual source-ordered
operand traces against the common final source and retained operator evidence. -/
theorem ordinaryBinary_expressionTypingBase_under_ambient_bounded
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : Ty} {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {fuel : Nat} {expression left right : Syntax.Expr}
    {operator : Syntax.Located Syntax.BinaryOp} {expected : Option Ty}
    {initial allocated leftState rightState :
      Frontend.SourceInference.State}
    {id : ExpressionId}
    {leftResult rightResult : InferredExpression}
    {inferred : Detail.OperatorInferenceResult}
    {result : InferredExpression × Frontend.SourceInference.State}
    {integerLiterals : List IntegerLiteralOrigin}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {sourceContext active : SourceSemantics.Context}
    {closedVariables : List TypeVarId}
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (parentSuccess : Detail.inferExprFuel (fuel + 1) inferenceContext
      expression expected initial = .ok result)
    (leftSuccess : Detail.inferExprFuel fuel inferenceContext left none
      allocated = .ok (leftResult, leftState))
    (rightSuccess : Detail.inferExprFuel fuel inferenceContext right none
      leftState = .ok (rightResult, rightState))
    (operatorSuccess : Detail.inferBinaryOperator inferenceContext
      operator.value leftResult.type rightResult.type expected integerLiterals
      rightState = .ok inferred)
    (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
      expression id inferred.type
      (.binary leftResult.id operator.value rightResult.id)
      inferred.requirements expected inferred.state = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (parentExtension : TypingSourceExtends
      (result.2.toTypedSource roots) (evidenceState.toTypedSource roots))
    (rightIntegerSubset :
      rightState.integerLiterals ⊆ result.2.integerLiterals)
    (parentIntegerSubset :
      result.2.integerLiterals ⊆ evidenceState.integerLiterals)
    (rightPatternSubset :
      rightState.integerPatterns ⊆ result.2.integerPatterns)
    (parentPatternSubset :
      result.2.integerPatterns ⊆ evidenceState.integerPatterns)
    (parentRequirementsSubset :
      result.2.requirements ⊆ evidenceState.requirements)
    (childSound : ExpressionChildTypingCallback (fuel + 1)
      inferenceContext (evidenceState.toTypedSource roots)
      finalized.typedSource evidenceState active finalized.substitution roots)
    (rightReady : rightState.InferenceReady)
    (leftBelow : leftResult.type.VariablesBelow
      rightState.inference.next)
    (rightBelow : rightResult.type.VariablesBelow
      rightState.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow rightState.inference.next)
    (integerLiteralsSubset :
      integerLiterals ⊆ resources.finalState.integerLiterals)
    (integerLiteralTargetsSupported : ∀ origin,
      origin ∈ resources.finalState.integerLiterals →
        resources.finalState.inference.substitution.apply
          (.variable origin.metavariable) = .word ∨
        resources.finalState.inference.substitution.apply
          (.variable origin.metavariable) = .integer)
    (substitutionExtends : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (activeCatalog : SignatureCatalogWellFormed active.signatures)
    (activeBinders : TypeParameterBindersWellFormed active)
    (sourceBinders : TypeParameterBindersWellFormed sourceContext)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (selectedTraitName : ∀ {selectedTrait : Resolved.DeclarationId}
      {traitName : String},
      Detail.operatorTrait? inferenceContext traitName =
          .ok (some selectedTrait) →
        (inferenceContext.signatures.trait? selectedTrait).map (·.name) =
          some traitName)
    (traitSuccess : Detail.conventionalTraitWithArity? inferenceContext
      "Coerce" 2 = .ok (some trait))
    (profileSuccess : Detail.coercionMethodProfile? inferenceContext trait =
      .ok (some profile))
    (traitName : (inferenceContext.signatures.trait? trait).map (·.name) =
      some "Coerce")
    (activeSignaturesEq : active.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (activeRequirementsEq : active.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    (assumptionsMono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        active.assumptions)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots)
      finalized.typedSource active finalized.substitution result.1 := by
  let children := ordinaryBinary_childProvenances allocationEq parentSuccess
    leftSuccess rightSuccess operatorSuccess recordSuccess initialBelow
    parentExtension rightIntegerSubset parentIntegerSubset
    rightPatternSubset parentPatternSubset parentRequirementsSubset
  have leftType : ExpressionHasType finalized.typedSource active
      leftResult.id (finalized.substitution.apply leftResult.type) :=
    resources.expressionHasType_of_childProvenance childSound children.1
      sourceBinders signaturesEq parametersEq ownerEq residual contextValid
  have rightType : ExpressionHasType finalized.typedSource active
      rightResult.id (finalized.substitution.apply rightResult.type) :=
    resources.expressionHasType_of_childProvenance childSound children.2
      sourceBinders signaturesEq parametersEq ownerEq residual contextValid
  have parentToSemantic : TypingSourceExtends
      ((result.2.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource := by
    have evidenceToSemantic : TypingSourceExtends
        ((evidenceState.toTypedSource roots).applySubstitution
          finalized.substitution) finalized.typedSource := by
      rw [resources.source_eq]
      exact .refl _
    exact TypingSourceExtends.trans
      (parentExtension.applySubstitution finalized.substitution)
      evidenceToSemantic
  have retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) finalized.typedSource result.1.id :=
    ExpressionRequirementsRetainedAt.ofTypingSourceExtends
      finalized.substitution parentToSemantic
  have finalRequirementsSubset : result.2.requirements ⊆
      resources.finalState.requirements := by
    rw [resources.requirements_eq]
    exact parentRequirementsSubset
  have finalSubstitutionExtends :
      resources.finalState.inference.substitution.SemanticallyExtends
        result.2.inference.substitution := by
    simpa only [← resources.substitution_eq] using substitutionExtends
  have finalContextValid : FlexibleSubstitution.ContextSubstitutionValid
      resources.finalState.inference.substitution closedVariables
      sourceContext active := by
    simpa only [← resources.substitution_eq] using contextValid
  simpa only [← resources.substitution_eq] using
    (inferBinaryOperator_recordExpressionWithExpected_success_expressionTypingBase_scoped_of_retained
      (later := resources.finalState)
      (base := finalizedRequirementContext inferenceContext finalized)
      operatorSuccess recordSuccess
      (by simpa only [← resources.substitution_eq] using leftType)
      (by simpa only [← resources.substitution_eq] using rightType)
      rightReady leftBelow rightBelow expectedBelow integerLiteralsSubset
      integerLiteralTargetsSupported finalSubstitutionExtends
      finalRequirementsSubset retained activeCatalog activeBinders
      traitSuccess profileSuccess catalog finalContextValid signaturesEq
      selectedTraitName traitName resources.solve_success
      resources.solved_context_eq resources.ledger resources.ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered)

/-- A selected unary operator supplies exactly one source-ordered argument
base; the callback is invoked only for the actual operand inference trace. -/
theorem selectedUnary_argumentTypingBases_of_retainedChild
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {operand : Syntax.Expr} {expected : Option Ty}
    {initial final evidenceState : Frontend.SourceInference.State}
    {inferred : InferredExpression} {roots : List NodeId}
    {semanticSource evidenceSource : TypedSource}
    {active : SourceSemantics.Context} {substitution : Substitution}
    (fuel_lt : fuel < parentFuel)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (success : Detail.inferExprFuel fuel inferenceContext operand expected
      initial = .ok (inferred, final))
    (integerSubset : final.integerLiterals ⊆ evidenceState.integerLiterals)
    (integerPatternSubset :
      final.integerPatterns ⊆ evidenceState.integerPatterns)
    (requirementsSubset : final.requirements ⊆ evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (final.toTypedSource roots) evidenceSource inferred.id)
    (childSound : RetainedExpressionChildTypingCallback parentFuel
      inferenceContext (final.toTypedSource roots) semanticSource
      evidenceSource evidenceState active substitution roots) :
    ArgumentTypingBasesValid (final.toTypedSource roots) semanticSource
      active substitution [inferred] := by
  exact .cons (childSound {
    fuel
    expression := operand
    expected
    initial
    final
    inferred
    fuel_lt
    initialNodesBelow := initialBelow
    success
    sourceExtension := TypingSourceExtends.refl _
    integerLiteralsSubset := integerSubset
    integerPatternsSubset := integerPatternSubset
    requirementsSubset
  } retained) .nil

/-- Two selected binary operands are assembled in source order.  The earlier
operand base is weakened to the state at which the later operand completed;
the node-prefix premise concerns only the pre-attachment traversal. -/
theorem selectedBinary_argumentTypingBases_of_retainedChildren
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {left right : Syntax.Expr}
    {initial leftState rightState evidenceState :
      Frontend.SourceInference.State}
    {leftResult rightResult : InferredExpression}
    {roots : List NodeId}
    {semanticSource evidenceSource : TypedSource}
    {active : SourceSemantics.Context} {substitution : Substitution}
    (fuel_lt : fuel < parentFuel)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (leftSuccess : Detail.inferExprFuel fuel inferenceContext left none
      initial = .ok (leftResult, leftState))
    (leftToRight : TypingSourceExtends (leftState.toTypedSource roots)
      (rightState.toTypedSource roots))
    (rightBelow : leftState.NodesBelowNextOccurrence)
    (rightSuccess : Detail.inferExprFuel fuel inferenceContext right none
      leftState = .ok (rightResult, rightState))
    (leftIntegerSubset :
      leftState.integerLiterals ⊆ evidenceState.integerLiterals)
    (leftPatternSubset :
      leftState.integerPatterns ⊆ evidenceState.integerPatterns)
    (leftRequirementsSubset :
      leftState.requirements ⊆ evidenceState.requirements)
    (rightIntegerSubset :
      rightState.integerLiterals ⊆ evidenceState.integerLiterals)
    (rightPatternSubset :
      rightState.integerPatterns ⊆ evidenceState.integerPatterns)
    (rightRequirementsSubset :
      rightState.requirements ⊆ evidenceState.requirements)
    (leftRetained : ExpressionRequirementsRetainedAt
      (leftState.toTypedSource roots) evidenceSource leftResult.id)
    (rightRetained : ExpressionRequirementsRetainedAt
      (rightState.toTypedSource roots) evidenceSource rightResult.id)
    (childSound : RetainedExpressionChildTypingCallback parentFuel
      inferenceContext (rightState.toTypedSource roots) semanticSource
      evidenceSource evidenceState active substitution roots) :
    ArgumentTypingBasesValid (rightState.toTypedSource roots) semanticSource
      active substitution [leftResult, rightResult] := by
  have leftBase : ExpressionTypingBase (leftState.toTypedSource roots)
      semanticSource active substitution leftResult := childSound {
    fuel
    expression := left
    expected := none
    initial
    final := leftState
    inferred := leftResult
    fuel_lt
    initialNodesBelow := initialBelow
    success := leftSuccess
    sourceExtension := leftToRight
    integerLiteralsSubset := leftIntegerSubset
    integerPatternsSubset := leftPatternSubset
    requirementsSubset := leftRequirementsSubset
  } leftRetained
  have rightBase : ExpressionTypingBase (rightState.toTypedSource roots)
      semanticSource active substitution rightResult := childSound {
    fuel
    expression := right
    expected := none
    initial := leftState
    final := rightState
    inferred := rightResult
    fuel_lt
    initialNodesBelow := rightBelow
    success := rightSuccess
    sourceExtension := TypingSourceExtends.refl _
    integerLiteralsSubset := rightIntegerSubset
    integerPatternsSubset := rightPatternSubset
    requirementsSubset := rightRequirementsSubset
  } rightRetained
  exact .cons (leftBase.weakenNodeSource leftToRight.nodes_prefix)
    (.cons rightBase .nil)

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceExpressionRecursiveSoundness
/-!
The fuel-recursive expression theorem is kept downstream of both the
syntax-directed expression bridges and the corresponding statement contract.
This file first records the finalization adapters which make that mutual
interface independent of an artificial, fixed pre-substitution semantic
context.  Such a context cannot remain fixed across source-ordered `let`
bindings, whereas the final substitution's validated range is stable for the
whole body.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

private theorem mem_freeVariables_foldl_application_iff_recursive
    (metavariable : TypeVarId) (head : Ty) (arguments : List Ty) :
    metavariable ∈ (arguments.foldl Ty.application head).freeVariables ↔
      metavariable ∈ head.freeVariables ∨
        ∃ argument, argument ∈ arguments ∧
          metavariable ∈ argument.freeVariables := by
  induction arguments generalizing head with
  | nil => simp
  | cons argument arguments induction =>
      rw [List.foldl_cons, induction,
        SourceSemantics.mem_freeVariables_application_iff]
      simp only [List.mem_cons]
      constructor
      · rintro ((headMember | argumentMember) | tailMember)
        · exact Or.inl headMember
        · exact Or.inr ⟨argument, Or.inl rfl, argumentMember⟩
        · rcases tailMember with ⟨candidate, candidateMember, occurs⟩
          exact Or.inr ⟨candidate, Or.inr candidateMember, occurs⟩
      · rintro (headMember | ⟨candidate, candidateMember, occurs⟩)
        · exact Or.inl (Or.inl headMember)
        · rcases candidateMember with rfl | candidateMember
          · exact Or.inl (Or.inr occurs)
          · exact Or.inr ⟨candidate, candidateMember, occurs⟩

private theorem mem_freeVariables_nominal_iff_recursive
    {metavariable : TypeVarId} {declaration : Resolved.DeclarationId}
    {arguments : List Ty} :
    metavariable ∈ (Ty.nominal declaration arguments).freeVariables ↔
      ∃ argument, argument ∈ arguments ∧
        metavariable ∈ argument.freeVariables := by
  rw [Ty.nominal, Ty.applyMany,
    mem_freeVariables_foldl_application_iff_recursive]
  simp [Ty.freeVariables]

private theorem typesWellScoped_of_each_admissible_within
    {context : SourceSemantics.Context} {outer : Ty} {types : List Ty}
    (each : ∀ type, type ∈ types → TypeAdmissible context type)
    (included : ∀ type, type ∈ types → ∀ metavariable,
      metavariable ∈ type.freeVariables →
        metavariable ∈ outer.freeVariables) :
    TypesWellScoped context (admissibleTypeVariables context outer) types := by
  induction types with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons
        ((each head (by simp)).typeWellScopedWithin
          (included head (by simp)))
        (induction
          (fun type member => each type (by simp [member]))
          (fun type member => included type (by simp [member])))

/-- Applying a structurally validated inference substitution to a
structurally validated inference type produces an admissible type directly in
the active residually-open context.  Unlike the older context-closure bridge,
this statement needs no parallel unsubstituted local context and therefore
survives sequential introduction of local binders. -/
theorem inferenceTypeFormationValidated_apply_typeAdmissible
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeParameterId}
    {flexibleVariables : List TypeVarId}
    {type : Ty} {substitution : Substitution}
    {active : SourceSemantics.Context}
    (validated : InferenceTypeFormationValidated signatures owner parameters
      flexibleVariables type)
    (range : InferenceSubstitutionRangeFormationValidated signatures owner
      parameters substitution)
    (binders : TypeParameterBindersWellFormed active)
    (signaturesEq : active.signatures = signatures)
    (parametersEq : active.typeParameters = parameters)
    (ownerEq : active.currentDeclaration = some owner)
    (residual : active.residualTypeVariables = true) :
    TypeAdmissible active (substitution.apply type) := by
  refine InferenceTypeFormationValidated.rec
    (motive_1 := fun current _ =>
      TypeAdmissible active (substitution.apply current))
    (motive_2 := fun types _ => ∀ current, current ∈ types →
      TypeAdmissible active (substitution.apply current))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ validated
  · intro metavariable _
    cases found : substitution.lookup? metavariable with
    | none =>
        simp only [Substitution.apply, found, Option.getD_none]
        exact TypeAdmissible.variableOfResidual binders residual metavariable
    | some replacement =>
        simp only [Substitution.apply, found, Option.getD_some]
        exact InferenceTypeFormationValidated.typeAdmissible
          (range metavariable replacement
            (TypeSystem.Substitution.lookup?_eq_some_mem found))
          binders signaturesEq parametersEq ownerEq residual
  · intro parameter bound owned
    exact {
      binders
      typeWellScoped := .parameter
        (by simpa [parametersEq] using bound)
        (ownerEq.trans (congrArg some owned.symm))
    }
  · intro builtin
    exact TypeAdmissible.builtin binders builtin
  · intro dataType arguments cataloged arity _ argumentsInduction
    rw [StructuralSubstitution.applyFlexible_nominal]
    refine {
      binders
      typeWellScoped := .nominal dataType
        (arguments.map substitution.apply)
        (by simpa [signaturesEq] using cataloged)
        (by simpa using arity) ?_
    }
    apply typesWellScoped_of_each_admissible_within
    · intro argument member
      rcases List.mem_map.mp member with ⟨sourceArgument, sourceMember, rfl⟩
      exact argumentsInduction sourceArgument sourceMember
    · intro argument member metavariable occurs
      rw [mem_freeVariables_nominal_iff_recursive]
      exact ⟨argument, member, occurs⟩
  · intro contract arguments cataloged arity _ argumentsInduction
    rw [StructuralSubstitution.applyFlexible_nominal]
    refine {
      binders
      typeWellScoped := .contractNominal contract
        (arguments.map substitution.apply)
        (by simpa [signaturesEq] using cataloged)
        (by simpa using arity) ?_
    }
    apply typesWellScoped_of_each_admissible_within
    · intro argument member
      rcases List.mem_map.mp member with ⟨sourceArgument, sourceMember, rfl⟩
      exact argumentsInduction sourceArgument sourceMember
    · intro argument member metavariable occurs
      rw [mem_freeVariables_nominal_iff_recursive]
      exact ⟨argument, member, occurs⟩
  · intro parameter result _ _ parameterInduction resultInduction
    exact TypeAdmissible.function parameterInduction resultInduction
  · intro left right _ _ leftInduction rightInduction
    exact TypeAdmissible.product leftInduction rightInduction
  · intro key value _ _ keyInduction valueInduction
    exact TypeAdmissible.mapping keyInduction valueInduction
  · intro inner _ innerInduction
    exact TypeAdmissible.proxy innerInduction
  · intro inner _ innerInduction
    exact TypeAdmissible.comptime innerInduction
  · intro current member
    simp at member
  · intro head tail _ _ headInduction tailInduction current member
    rcases List.mem_cons.mp member with rfl | tailMember
    · exact headInduction
    · exact tailInduction current tailMember

/-- `Coerce` profile instantiation commutes with an inference substitution
when both the raw and normalized profile are interpreted in the same active
semantic context.  Catalog membership is unchanged, so no source-to-target
context closure is needed. -/
theorem coercionProfileInstantiates_apply_in_active
    {substitution : Substitution} {active : SourceSemantics.Context}
    {sourceType targetType : Ty} {primary : ProgramPredicate}
    {methodPredicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed active.signatures)
    (profile : CoercionProfileInstantiates active sourceType targetType
      primary methodPredicates) :
    CoercionProfileInstantiates active
      (substitution.apply sourceType) (substitution.apply targetType)
      (TypedTraitResolution.applySubstitution substitution primary)
      (methodPredicates.map
        (TypedTraitResolution.applySubstitution substitution)) := by
  cases profile with
  | @intro signature method fromParameter toParameter signatureMem nameEq
      parametersEq methodUnique parameterTypesEq returnTypesEq =>
      have signatureWellFormed := catalog.traits_semantic signature signatureMem
      have methodFiltered : method ∈
          signature.methods.filter
            (fun candidate => candidate.name == "coerce") := by
        rw [methodUnique]
        simp
      have methodMem : method ∈ signature.methods :=
        (List.mem_filter.mp methodFiltered).1
      have methodWellFormed := signatureWellFormed.methods method methodMem
      have innerExact : SourceSemantics.ParameterSubstitution.Exact
          [(fromParameter, sourceType), (toParameter, targetType)]
          signature.parameters := by
        constructor
        · exact signatureWellFormed.parameters_nodup
        · rw [parametersEq]
          simp [SourceSemantics.ParameterSubstitution.domain]
      have parameterCompose :=
        FlexibleSubstitution.TypesWellScoped.applyFlexible_composeParameters
          (context := signatureContext active.signatures signature.id
            signature.parameters
            (signature.wherePredicates ++ method.wherePredicates))
          substitution
          [(fromParameter, sourceType), (toParameter, targetType)] innerExact
          (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
            methodWellFormed.parameter_types)
      have returnCompose :=
        FlexibleSubstitution.TypesWellScoped.applyFlexible_composeParameters
          (context := signatureContext active.signatures signature.id
            signature.parameters
            (signature.wherePredicates ++ method.wherePredicates))
          substitution
          [(fromParameter, sourceType), (toParameter, targetType)] innerExact
          (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
            methodWellFormed.return_types)
      have predicateCompose :=
        FlexibleSubstitution.PredicatesWellFormed.applyFlexible_composeParameters
          (context := signatureContext active.signatures signature.id
            signature.parameters
            (signature.wherePredicates ++ method.wherePredicates))
          substitution
          [(fromParameter, sourceType), (toParameter, targetType)] innerExact
          methodWellFormed.predicates
      change CoercionProfileInstantiates active
        (substitution.apply sourceType) (substitution.apply targetType)
        { trait := .declaration signature.id
          subject := substitution.apply sourceType
          arguments := [substitution.apply targetType] }
        ((method.wherePredicates.map
          (ProgramPredicate.applyParameters
            [(fromParameter, sourceType), (toParameter, targetType)])).map
              (TypedTraitResolution.applySubstitution substitution))
      rw [predicateCompose]
      exact .intro signatureMem nameEq parametersEq methodUnique
        (by
          change method.parameterTypes.map
              (FlexibleSubstitution.ParameterSubstitution.mapRange substitution
                [(fromParameter, sourceType),
                  (toParameter, targetType)]).apply =
            [substitution.apply sourceType]
          rw [← parameterCompose, parameterTypesEq]
          rfl)
        (by
          change method.returnTypes.map
              (FlexibleSubstitution.ParameterSubstitution.mapRange substitution
                [(fromParameter, sourceType),
                  (toParameter, targetType)]).apply =
            [substitution.apply targetType]
          rw [← returnCompose, returnTypesEq]
          rfl)

/-- One planned coercion edge remains a valid `Coerce` profile after the
whole-body substitution is applied, interpreted directly in the active
context. -/
theorem plannedCoercionStep_profileInstantiatesAfterSubstitution_in_active
    {inferenceContext : Frontend.SourceInference.Context}
    {active : SourceSemantics.Context} {substitution : Substitution}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {planned : Detail.PlannedCoercionStep}
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (consistent :
      Detail.PlannedCoercionStep.ProfileConsistent trait profile planned) :
    CoercionProfileInstantiates active
      (substitution.apply planned.source)
      (substitution.apply planned.target)
      (TypedTraitResolution.applySubstitution substitution planned.predicate)
      (planned.methodPredicates.map
        (TypedTraitResolution.applySubstitution substitution)) := by
  have raw : CoercionProfileInstantiates active planned.source planned.target
      planned.predicate planned.methodPredicates := by
    simpa [consistent.predicate_eq] using
      coercionMethodProfile?_some_instantiates signaturesEq traitName
        profileSuccess consistent.methodPredicates_eq
  exact coercionProfileInstantiates_apply_in_active catalog raw

private theorem committed_member_has_planned_correspondence_in_active
    {requirements : List Requirement}
    {plan : List Detail.PlannedCoercionStep}
    {steps : List CoercionStep}
    (corresponds : Detail.CoercionPlanCommitCorresponds requirements
      plan steps)
    {committed : CoercionStep}
    (member : committed ∈ steps) :
    ∃ planned, planned ∈ plan ∧
      Detail.PlannedCoercionStep.CommitCorresponds requirements
        planned committed := by
  induction corresponds with
  | nil => simp at member
  | @cons planned committed plan steps head tail induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨planned, by simp, head⟩
      · obtain ⟨candidate, candidateMember, candidateCorresponds⟩ :=
          induction member
        exact ⟨candidate, by simp [candidateMember], candidateCorresponds⟩

/-- A later whole-body substitution closes a committed coercion plan using
occurrence-scoped evidence, with all profile semantics interpreted directly
in the current active context. -/
theorem coercionPlan?_some_committedPathValid_at_scoped_in_active
    {inferenceContext : Frontend.SourceInference.Context}
    {solverContext : Frontend.SourceInference.Context}
    {state later : State} {source target : Ty}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {plan : List Detail.PlannedCoercionStep}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {ledgerSource : TypedSource} {occurrence : NodeId}
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (planSuccess :
      Detail.coercionPlan? inferenceContext state source target =
        .ok (some plan))
    (requirementsSubset :
      (Detail.commitCoercionPlan state plan).2.requirements ⊆
        later.requirements)
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered ledgerSource active occurrence)
    (occurs : ∀ id,
      id ∈ coercionRequirementIds
        (Detail.commitCoercionPlan state plan).1 →
      PrimaryRequirementOccursAt ledgerSource occurrence id) :
    CoercionPathValid active
      (later.inference.substitution.apply source)
      (later.inference.substitution.apply target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution
          later.inference.substitution)) := by
  have corresponds : Detail.CoercionPlanCommitCorresponds later.requirements
      plan (Detail.commitCoercionPlan state plan).1 :=
    (Detail.commitCoercionPlan_corresponds state plan).mono
      requirementsSubset
  have retainedStructural : Frontend.SourceInference.CoercionPath.isValid
      source target (Detail.commitCoercionPlan state plan).1 = true :=
    corresponds.isValid (Detail.coercionPlan?_some_isValid planSuccess)
  have normalizedStructural : Frontend.SourceInference.CoercionPath.isValid
      (later.inference.substitution.apply source)
      (later.inference.substitution.apply target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution
          later.inference.substitution)) = true :=
    Frontend.SourceInference.CoercionPath.isValid_applySubstitution
      later.inference.substitution retainedStructural
  apply CoercionPathValid.of_isValid normalizedStructural
  intro step stepMember
  obtain ⟨committed, committedMember, rfl⟩ := List.mem_map.mp stepMember
  obtain ⟨planned, plannedMember, correspondence⟩ :=
    committed_member_has_planned_correspondence_in_active corresponds
      committedMember
  have consistent := Detail.coercionPlan?_some_profileConsistent
    traitSuccess profileSuccess planSuccess planned plannedMember
  have methodPredicatesEq :
      planned.methodPredicates.map (Detail.applyPredicate later) =
        planned.methodPredicates.map
          (TypedTraitResolution.applySubstitution
            later.inference.substitution) := by
    apply List.map_congr_left
    intro predicate _
    rfl
  have profileInstantiates :=
    plannedCoercionStep_profileInstantiatesAfterSubstitution_in_active
      (substitution := later.inference.substitution) catalog signaturesEq
      traitName profileSuccess consistent
  have normalizedProfile : CoercionProfileInstantiates active
      (later.resolve planned.source) (later.resolve planned.target)
      (Detail.applyPredicate later planned.predicate)
      (planned.methodPredicates.map (Detail.applyPredicate later)) := by
    rw [methodPredicatesEq]
    simpa [State.resolve, TypeSystem.InferState.resolve,
      Detail.applyPredicate] using profileInstantiates
  apply committedCoercionStepValidAt (state := later) correspondence
    normalizedProfile solveSuccess solvedEq ledger ownership
    activeSignaturesEq activeRequirementsEq assumptionsMono covered
  intro id member
  apply occurs id
  unfold coercionRequirementIds
  exact List.mem_flatMap.mpr ⟨committed, committedMember, member⟩

/-- Expected-type fitting has a valid normalized output path in the active
context, using only the final scoped ledger and catalog. -/
theorem withExpected_success_coercionPathValid_scoped_in_active
    {inferenceContext : Frontend.SourceInference.Context}
    {solverContext : Frontend.SourceInference.Context}
    {state later : State} {actual : InferredExpression}
    {expected : Option Ty} {result : Detail.ExpectationResult}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {ledgerSource : TypedSource} {occurrence : NodeId}
    (success : Detail.withExpected inferenceContext state actual expected =
      .ok result)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (requirementsSubset : result.state.requirements ⊆ later.requirements)
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered ledgerSource active occurrence)
    (occurs : ∀ id, id ∈ coercionRequirementIds result.coercions →
      PrimaryRequirementOccursAt ledgerSource occurrence id) :
    CoercionPathValid active
      (later.inference.substitution.apply
        (result.state.resolve actual.type))
      (later.inference.substitution.apply result.expression.type)
      (result.coercions.map
        (CoercionStep.applySubstitution
          later.inference.substitution)) := by
  rcases Detail.withExpected_success_cases success with
    ⟨coercionsEq, _, typeEq⟩ |
      ⟨expectedType, plan, _, planSuccess, resultEq⟩
  · rw [coercionsEq]
    simp only [List.map_nil]
    rw [typeEq]
    exact .nil _
  · subst expected
    subst result
    change CoercionPathValid active
      (later.inference.substitution.apply
        ((Detail.commitCoercionPlan state plan).2.resolve actual.type))
      (later.inference.substitution.apply (state.resolve expectedType))
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution later.inference.substitution))
    rw [Detail.commitCoercionPlan_resolve]
    exact coercionPlan?_some_committedPathValid_at_scoped_in_active
      traitSuccess profileSuccess planSuccess requirementsSubset catalog
      signaturesEq traitName solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered occurs

/-- Ordinary expression recording closes directly in the active context.
This is the context-stable replacement for the older recorder bridge whose
only use of a parallel raw context was transport of the `Coerce` profile. -/
theorem
    recordExpressionWithExpected_success_ordinaryExpressionTypingBase_in_active
    {inferenceContext : Frontend.SourceInference.Context}
    {solverContext : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {rawType : Ty} {form : ExpressionForm}
    {owned : List RequirementId} {expected : Option Ty}
    {state later : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    {roots : List NodeId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    (success : Detail.recordExpressionWithExpected inferenceContext source id
      rawType form owned expected state localSchemeInstantiationStart =
        .ok result)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.2.inference.substitution)
    (requirementsSubset : result.2.requirements ⊆ later.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (formType : ExpressionFormHasRawType semanticSource active
      (form.applySubstitution later.inference.substitution)
      (later.inference.substitution.apply rawType) (.ordinary owned))
    (rawAdmissible : TypeAdmissible active
      (later.inference.substitution.apply rawType))
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base evidenceSource)
    (ownership : RequirementOwnership base evidenceSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered evidenceSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots) semanticSource active
      later.inference.substitution result.1 := by
  obtain ⟨fitted, fittedSuccess, resultExpressionEq, resultStateEq⟩ :=
    Detail.recordExpressionWithExpected_success_record success
  have recordedContains : ContainsExpression
      (result.2.toTypedSource roots) result.1.id {
        id := result.1.id
        span := source.span
        type := result.1.type
        form
        requirements := owned ++
          Detail.coercionRequirements fitted.coercions
        coercions := fitted.coercions
        localSchemeInstantiationStart
      } := by
    rw [resultExpressionEq, resultStateEq]
    exact recordNode_containsExpression fitted.state _ roots
  have fittedRequirementsSubset :
      fitted.state.requirements ⊆ later.requirements := by
    intro requirement member
    apply requirementsSubset
    rw [resultStateEq]
    exact member
  have fittedSubstitutionExtends :
      later.inference.substitution.SemanticallyExtends
        fitted.state.inference.substitution := by
    simpa [resultStateEq, State.recordNode] using substitutionExtends
  have occursOwned : ∀ requirement, requirement ∈ owned →
      PrimaryRequirementOccursAt evidenceSource
        (.expression result.1.id) requirement := by
    intro requirement member
    apply retained recordedContains
    simp [member]
  have occursCoercion : ∀ requirement,
      requirement ∈ coercionRequirementIds fitted.coercions →
        PrimaryRequirementOccursAt evidenceSource
          (.expression result.1.id) requirement := by
    intro requirement member
    apply retained recordedContains
    change requirement ∈
      owned ++ Detail.coercionRequirements fitted.coercions
    apply List.mem_append_right owned
    simpa [Detail.coercionRequirements, coercionRequirementIds] using member
  have ownedValid : RequirementIdsValid active owned :=
    ledger.requirementIdsValidAt ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono covered occursOwned
  have path :=
    withExpected_success_coercionPathValid_scoped_in_active
      fittedSuccess traitSuccess profileSuccess fittedRequirementsSubset
      catalog signaturesEq traitName solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered
      occursCoercion
  have rawEndpointEq :
      later.inference.substitution.apply (fitted.state.resolve rawType) =
        later.inference.substitution.apply rawType :=
    TypeSystem.InferState.apply_resolve_eq_apply fittedSubstitutionExtends
      rawType
  have finalPath : CoercionPathValid active
      (later.inference.substitution.apply rawType)
      (later.inference.substitution.apply result.1.type)
      (fitted.coercions.map
        (CoercionStep.applySubstitution
          later.inference.substitution)) := by
    rw [resultExpressionEq, ← rawEndpointEq]
    exact path
  have requirementsEq :
      owned ++ Detail.coercionRequirements fitted.coercions =
      owned ++ coercionRequirementIds
        (fitted.coercions.map
          (CoercionStep.applySubstitution
            later.inference.substitution)) := by
    rw [FlexibleSubstitution.coercionRequirementIds_applySubstitution]
    rfl
  refine ExpressionTypingBase.intro (plan := .ordinary owned)
    recordedContains (by rfl) ?_ rawAdmissible ?_
  · simpa [ExpressionNode.applySubstitution] using formType
  · exact ExpressionRequirementPlan.Valid.ordinary ownedValid finalPath
      requirementsEq

/-- The local-reference requirement spine needs only semantic substitution
extension from its allocation state to the whole solver state.  Allocator
growth and final-state `next` bounds are irrelevant to the normalized
predicate equality used by declarative evidence. -/
theorem localReferenceRequirementSequenceProves_afterSemanticExtension
    {solverContext : Frontend.SourceInference.Context}
    {instantiationState finalState : State}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {source : TypedSource} {occurrence : NodeId}
    {binder : TypedBinder} {instantiationStart : Nat}
    {ids : List RequirementId}
    (extension : finalState.inference.substitution.SemanticallyExtends
      instantiationState.inference.substitution)
    (corresponds : RequirementPredicatesCorrespond finalState.requirements
      ((instantiateLocalSchemePredicates
          (binder.scheme.instantiateWithSubstitution
            instantiationStart).substitution binder).map
        (Detail.applyPredicate instantiationState)) ids)
    (success : Detail.solveRequirements solverContext finalState
      finalState.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base source)
    (ownership : RequirementOwnership base source)
    (signaturesEq : active.signatures = base.signatures)
    (requirementsEq : active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered source active occurrence)
    (occurs : ∀ id, id ∈ ids →
      PrimaryRequirementOccursAt source occurrence id) :
    RequirementSequenceProves active ids
      ((instantiateLocalSchemePredicates
          (binder.scheme.instantiateWithSubstitution
            instantiationStart).substitution binder).map
        (TypedTraitResolution.applySubstitution
          finalState.inference.substitution)) := by
  have proves := solveRequirements_correspondingSequenceProvesAt corresponds
    success solvedEq ledger ownership signaturesEq requirementsEq
    assumptionsMono covered occurs
  simpa only [List.map_map, Function.comp_def, Detail.applyPredicate,
    TypedTraitResolution.applySubstitution_semanticallyExtends extension] using
      proves

/-- Whole-body finalization supplies an admissible range for its returned
substitution in every active context with the declaration's static scope. -/
theorem FinalInferenceResources.substitutionRangeAdmissible
    {wholeContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    {active : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed active)
    (signaturesEq : active.signatures = wholeContext.signatures)
    (parametersEq : active.typeParameters = wholeContext.typeParameters)
    (ownerEq : active.currentDeclaration =
      some wholeContext.scope.genericOwner)
    (residual : active.residualTypeVariables = true) :
    SubstitutionRangeAdmissible active finalized.substitution :=
  InferenceSubstitutionRangeFormationValidated.rangeAdmissible
    resources.range_formation binders signaturesEq parametersEq ownerEq
      residual

/-- A retained expression node has an admissible finalized type in the
current active context without a fixed source-side context-substitution
certificate. -/
theorem FinalInferenceResources.expressionTypeAdmissible_in_active
    {wholeContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    {node : ExpressionNode}
    (member : Node.expression node ∈
      (evidenceState.toTypedSource roots).nodes)
    {active : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed active)
    (signaturesEq : active.signatures = wholeContext.signatures)
    (parametersEq : active.typeParameters = wholeContext.typeParameters)
    (ownerEq : active.currentDeclaration =
      some wholeContext.scope.genericOwner)
    (residual : active.residualTypeVariables = true) :
    TypeAdmissible active (finalized.substitution.apply node.type) :=
  inferenceTypeFormationValidated_apply_typeAdmissible
    (resources.expressionTypeFormationValidated member)
    resources.range_formation binders signaturesEq parametersEq ownerEq
      residual

/-- The state/context facts shared by every recursive expression boundary.
Unlike `RecursiveStatementInvariant`, this record has no ambient return type:
expression inference preserves the active lexical context and needs only the
whole-finalization scope, allocator bounds, and final-substitution extension. -/
structure RecursiveExpressionInvariant
    (wholeContext : Frontend.SourceInference.Context)
    (finalized : Frontend.SourceInference.Result)
    (state : State) (semanticContext : SourceSemantics.Context) : Prop where
  active : ActiveLocalContextInvariant state finalized.substitution
    semanticContext
  ready : state.InferenceReady
  bindersBelow : state.LocalBindersBelowNextLocal
  nodesBelow : state.NodesBelowNextOccurrence
  schemeIsolation : ActiveSchemeQuantifierIsolation state
  substitutionExtension : finalized.substitution.SemanticallyExtends
    state.inference.substitution
  signaturesEq : semanticContext.signatures =
    (finalizedRequirementContext wholeContext finalized).signatures
  typeParametersEq : semanticContext.typeParameters =
    wholeContext.typeParameters
  declarationEq : semanticContext.currentDeclaration =
    some wholeContext.scope.genericOwner
  residual : semanticContext.residualTypeVariables = true
  solvedRequirementsEq : semanticContext.solvedRequirements =
    (finalizedRequirementContext wholeContext finalized).solvedRequirements
  assumptionsMono :
    (finalizedRequirementContext wholeContext finalized).assumptions ⊆
      semanticContext.assumptions

/-- Reserving an expression occurrence preserves every recursive expression
invariant, including the lexical quantifier-isolation certificate. -/
theorem RecursiveExpressionInvariant.allocateExpressionId
    {wholeContext : Frontend.SourceInference.Context}
    {finalized : Frontend.SourceInference.Result}
    {initial allocated : State} {id : ExpressionId}
    {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext)
    (allocationEq : initial.allocateExpressionId = (id, allocated)) :
    RecursiveExpressionInvariant wholeContext finalized allocated
      semanticContext := by
  have allocatedEq : initial.allocateExpressionId.2 = allocated :=
    congrArg Prod.snd allocationEq
  subst allocated
  refine {
    active := invariant.active.congr_localBinders (by rfl)
    ready := State.InferenceReady.allocateExpressionId invariant.ready
    bindersBelow :=
      State.allocateExpressionId_preserves_localBindersBelowNextLocal initial
        invariant.bindersBelow
    nodesBelow :=
      State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial
        invariant.nodesBelow
    schemeIsolation :=
      activeSchemeQuantifierIsolation_allocateExpressionId
        invariant.schemeIsolation allocationEq
    substitutionExtension := invariant.substitutionExtension
    signaturesEq := invariant.signaturesEq
    typeParametersEq := invariant.typeParametersEq
    declarationEq := invariant.declarationEq
    residual := invariant.residual
    solvedRequirementsEq := invariant.solvedRequirementsEq
    assumptionsMono := invariant.assumptionsMono
  }

/-- Forget the statement-only return bound from the mutual statement
invariant at an expression child boundary. -/
theorem RecursiveExpressionInvariant.ofStatement
    {wholeContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty} {finalized : Frontend.SourceInference.Result}
    {state : State} {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveStatementInvariant wholeContext expectedReturn
      finalized state semanticContext) :
    RecursiveExpressionInvariant wholeContext finalized state
      semanticContext := {
  active := invariant.active
  ready := invariant.ready
  bindersBelow := invariant.bindersBelow
  nodesBelow := invariant.nodesBelow
  schemeIsolation := invariant.schemeIsolation
  substitutionExtension := invariant.substitutionExtension
  signaturesEq := invariant.signaturesEq
  typeParametersEq := invariant.typeParametersEq
  declarationEq := invariant.declarationEq
  residual := invariant.residual
  solvedRequirementsEq := invariant.solvedRequirementsEq
  assumptionsMono := invariant.assumptionsMono
}

theorem RecursiveExpressionInvariant.signatures_eq_whole
    {wholeContext : Frontend.SourceInference.Context}
    {finalized : Frontend.SourceInference.Result}
    {state : State} {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveExpressionInvariant wholeContext finalized state
      semanticContext) :
    semanticContext.signatures = wholeContext.signatures := by
  simpa [finalizedRequirementContext, Context.withSolvedRequirements,
    Context.withAssumptions, Context.ofSignatures] using
      invariant.signaturesEq

theorem RecursiveExpressionInvariant.typeParameterBinders
    {wholeContext : Frontend.SourceInference.Context}
    {finalized : Frontend.SourceInference.Result}
    {state : State} {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveExpressionInvariant wholeContext finalized state
      semanticContext)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters) :
    TypeParameterBindersWellFormed semanticContext := by
  let declarationScope := declarationContext wholeContext.signatures
    wholeContext.scope.genericOwner wholeContext.typeParameters [] []
  have declarationBinders : TypeParameterBindersWellFormed
      declarationScope := by
    exact
      Solcore.SourceSemantics.SignatureParametersWellFormed.declarationContextBinders
        canonical [] []
  exact StructuralSubstitution.TypeParameterBindersWellFormed.transportContext
    (source := declarationScope) (target := semanticContext)
    (by
      simpa [declarationScope, declarationContext, signatureContext,
        Context.withResidualTypeVariables, Context.withSolvedRequirements,
        Context.withAssumptions, Context.forDeclaration,
        Context.ofSignatures] using
          invariant.typeParametersEq)
    (by
      simpa [declarationScope, declarationContext, signatureContext,
        Context.withResidualTypeVariables, Context.withSolvedRequirements,
        Context.withAssumptions, Context.forDeclaration,
        Context.ofSignatures] using
          invariant.declarationEq)
    declarationBinders

/-- The numeric-literal branch closes directly in the active recursive
context.  This version uses finalization's validated literal ledger and the
context-stable ordinary recorder bridge, so it does not require a parallel
unsubstituted semantic context. -/
theorem
    inferExprFuel_success_numericLiteral_expressionTypingBase_retained_in_active
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    {fuel : Nat} {expression : Syntax.Expr}
    {literal : Syntax.CoreLiteral} {source : Syntax.CoreLiteralValue}
    {rawValue : Nat} {expected : Option Ty}
    {initial allocated : State} {id : ExpressionId}
    {inferred : InferredExpression} {resultState : State}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {semanticSource : TypedSource}
    {active : SourceSemantics.Context}
    (expressionEq : expression.value = .literal literal)
    (literalEq : literal.value = source)
    (decoded : Frontend.numericLiteralValue? source = some rawValue)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (integerLiteralsSubset : resultState.integerLiterals ⊆
      evidenceState.integerLiterals)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (fun row => row.name) =
        some "Coerce")
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  let rawType := allocated.fresh.1
  let freshState := allocated.fresh.2
  let addition := freshState.addRequirementWithId
    (ProgramSignatures.builtinIntPredicate rawType)
  let origin : IntegerLiteralOrigin := {
    metavariable := ⟨allocated.inference.next⟩
    expression := id
    requirement := addition.1
  }
  let literalState : State := {
    addition.2 with
    integerLiterals := addition.2.integerLiterals ++ [origin]
  }
  let resolution : IntegerLiteralResolution := {
    rawValue
    targetType := rawType
    requirement := addition.1
  }
  obtain ⟨recorded, originMember, requirementMember⟩ :=
    Detail.inferExprFuel_success_numericLiteral_record expressionEq literalEq
      decoded allocationEq success
  have originMemberFinal : origin ∈ evidenceState.integerLiterals :=
    integerLiteralsSubset originMember
  have requirementMemberFinal :
      ({ id := origin.requirement
         predicate := ProgramSignatures.builtinIntPredicate
           (.variable origin.metavariable) } : Requirement) ∈
        evidenceState.requirements := by
    apply requirementsSubset
    simpa [origin, addition, freshState, rawType,
      State.fresh, TypeSystem.InferState.fresh] using requirementMember
  obtain ⟨coercions, recordedContains⟩ :=
    recordExpressionWithExpected_success_containsExpression recorded roots
  have occurs : PrimaryRequirementOccursAt finalized.typedSource
      (.expression inferred.id) resolution.requirement := by
    apply retained recordedContains
    change resolution.requirement ∈
      [addition.1] ++ Detail.coercionRequirements coercions
    simp [resolution]
  have literalValid : IntegerLiteralValid active source
      (resolution.applySubstitution finalized.substitution) := by
    apply resources.integerLiteralValidAt
      (origin := origin) (decoded := by simpa [resolution] using decoded)
    · simp [resolution, origin, rawType, State.fresh,
        TypeSystem.InferState.fresh]
    · rfl
    · exact originMemberFinal
    · exact requirementMemberFinal
    · exact invariant.signaturesEq
    · exact invariant.solvedRequirementsEq
    · exact invariant.assumptionsMono
    · exact covered
    · exact occurs
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.integerLiteral source resolution).applySubstitution
        finalized.substitution)
      (finalized.substitution.apply rawType) (.ordinary [addition.1]) := by
    simpa [ExpressionForm.applySubstitution, resolution,
      IntegerLiteralResolution.applySubstitution] using
        (ExpressionFormHasRawType.integerLiteral literalValid)
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply rawType) := by
    simpa [resolution, IntegerLiteralResolution.applySubstitution] using
      literalValid.target_type_admissible
        (invariant.typeParameterBinders canonical)
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have finalSubstitutionExtends :
      resources.finalState.inference.substitution.SemanticallyExtends
        resultState.inference.substitution := by
    simpa only [finalSubstitutionEq] using resultSubstitutionExtension
  have requirementsSubsetFinal :
      resultState.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirementsSubset member
  have activeSignaturesEq : active.signatures =
      inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_in_active
      (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      recorded finalSubstitutionExtends requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      traitSuccess profileSuccess activeCatalog activeSignaturesEq traitName
      resources.solve_success resources.solved_context_eq resources.ledger
      resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered)

/-- The builtin-Boolean identifier is source-independent; only its optional
output coercion consults the whole finalized ledger. -/
theorem
    inferExprFuel_success_builtinBooleanIdentifier_expressionTypingBase_retained_in_active
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    {fuel : Nat} {expression : Syntax.Expr} {expected : Option Ty}
    {initial allocated resultState : State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {inferred : InferredExpression}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = none)
    (isBoolean :
      (name.value == "true" || name.value == "false") = true)
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (fun row => row.name) =
        some "Coerce")
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  have recorded : Detail.recordExpressionWithExpected inferenceContext
      expression id .bool
      (.reference name.value (.builtinBoolean (name.value == "true"))) []
      expected allocated = .ok (inferred, resultState) :=
    Detail.inferExprFuel_success_builtinBooleanIdentifier_record expressionEq
      allocationEq lookupEq isBoolean success
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.reference name.value
        (.builtinBoolean (name.value == "true"))).applySubstitution
          finalized.substitution)
      (finalized.substitution.apply .bool) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution,
      ReferenceResolution.applySubstitution] using
      (ExpressionFormHasRawType.reference (source := semanticSource)
        (ReferenceUseValid.builtinBoolean (context := active)
          (name.value == "true")))
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply .bool) := by
    simpa using TypeAdmissible.bool
      (invariant.typeParameterBinders canonical)
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have requirementsSubsetFinal :
      resultState.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirementsSubset member
  have activeSignaturesEq : active.signatures =
      inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_in_active
      (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      recorded
      (by simpa only [finalSubstitutionEq] using resultSubstitutionExtension)
      requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      traitSuccess profileSuccess activeCatalog activeSignaturesEq traitName
      resources.solve_success resources.solved_context_eq resources.ledger
      resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered)

/-- A builtin-function identifier has a closed, catalog-independent raw
reference type in the active context. -/
theorem
    inferExprFuel_success_builtinFunctionIdentifier_expressionTypingBase_retained_in_active
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    {fuel : Nat} {expression : Syntax.Expr} {expected : Option Ty}
    {initial allocated resultState : State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {function : BuiltinFunctionId} {inferred : InferredExpression}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = none)
    (notBoolean :
      (name.value == "true" || name.value == "false") = false)
    (functionsEq : Detail.functionsNamed inferenceContext name.value =
      .ok [])
    (builtinEq : Frontend.builtinFunctionNamed? name.value = some function)
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (fun row => row.name) =
        some "Coerce")
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  have recorded : Detail.recordExpressionWithExpected inferenceContext
      expression id function.type
      (.reference name.value (.builtinFunction function)) [] expected
      allocated = .ok (inferred, resultState) :=
    Detail.inferExprFuel_success_builtinFunctionIdentifier_record expressionEq
      allocationEq lookupEq notBoolean functionsEq builtinEq success
  have fixedType : finalized.substitution.apply function.type =
      function.type := by
    cases function <;>
      simp [BuiltinFunctionId.type, BuiltinFunctionId.parameterTypes,
        BuiltinFunctionId.returnType, Ty.productMany]
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.reference name.value
        (.builtinFunction function)).applySubstitution
          finalized.substitution)
      (finalized.substitution.apply function.type) (.ordinary []) := by
    rw [fixedType]
    simpa [ExpressionForm.applySubstitution,
      ReferenceResolution.applySubstitution] using
      (ExpressionFormHasRawType.reference (source := semanticSource)
        (ReferenceUseValid.builtinFunction (context := active) function))
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply function.type) := by
    rw [fixedType]
    exact TypeAdmissible.builtinFunction
      (invariant.typeParameterBinders canonical) function
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have requirementsSubsetFinal :
      resultState.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirementsSubset member
  have activeSignaturesEq : active.signatures =
      inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_in_active
      (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      recorded
      (by simpa only [finalSubstitutionEq] using resultSubstitutionExtension)
      requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      traitSuccess profileSuccess activeCatalog activeSignaturesEq traitName
      resources.solve_success resources.solved_context_eq resources.ledger
      resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered)

/-- Canonical local-scheme instantiation closes directly in the active
recursive context.  The allocation and no-capture certificates remain
explicit because they are supplied by the recursive ledger/provenance
invariants rather than by a fixed source-side substitution context. -/
theorem
    inferExprFuel_success_localIdentifier_expressionTypingBase_retained_in_active
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    {fuel : Nat} {expression : Syntax.Expr} {expected : Option Ty}
    {initial allocated resultState : State}
    {id : ExpressionId} {name : Syntax.Identifier} {binder : TypedBinder}
    {inferred : InferredExpression}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    (certificate :
      let instantiationStart := allocated.inference.next
      let instantiated :=
        binder.scheme.instantiateWithSubstitution instantiationStart
      let inference := { allocated.inference with next := instantiated.next }
      let advanced : State := { allocated with inference }
      let predicates := binder.schemeRequirements.map fun requirement =>
        Detail.applyPredicate advanced
          (TypedTraitResolution.applySubstitution instantiated.substitution
            requirement.predicate)
      State.LookupBinderRequirementAllocationCertificate advanced binder
        predicates)
    (noCapture : Detail.LocalBinderInstantiationNoCapture
      finalized.substitution binder)
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (fun row => row.name) =
        some "Coerce")
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  let instantiationStart := allocated.inference.next
  let instantiated :=
    binder.scheme.instantiateWithSubstitution instantiationStart
  let inference := { allocated.inference with next := instantiated.next }
  let advanced : State := { allocated with inference }
  let predicates := binder.schemeRequirements.map fun requirement =>
    Detail.applyPredicate advanced
      (TypedTraitResolution.applySubstitution instantiated.substitution
        requirement.predicate)
  let allocation := advanced.addRequirementsWithIds predicates
  change State.LookupBinderRequirementAllocationCertificate advanced binder
    predicates at certificate
  have recorded : Detail.recordExpressionWithExpected inferenceContext
      expression id (advanced.resolve instantiated.body)
      (.reference name.value (.local binder.id)) allocation.1 expected
      allocation.2
      (localSchemeInstantiationStart := some instantiationStart) =
        .ok (inferred, resultState) := by
    simpa only [instantiationStart, instantiated, inference, advanced,
      predicates, allocation] using
        (Detail.inferExprFuel_success_localIdentifier_record expressionEq
          allocationEq lookupEq success)
  have branchFacts := inferExprFuel_success_localIdentifier_facts
    expressionEq allocationEq lookupEq success certificate roots
  change ∃ coercions,
      ContainsExpression (resultState.toTypedSource roots) inferred.id {
        id := inferred.id
        span := expression.span
        type := inferred.type
        form := .reference name.value (.local binder.id)
        requirements := allocation.1 ++
          Detail.coercionRequirements coercions
        coercions
        localSchemeInstantiationStart := some instantiationStart
      } ∧
      allocation.1.Nodup ∧
      (∀ requirement, requirement ∈ allocation.1 →
        requirement ∉ localSchemeTemplateIds binder) ∧
      RequirementPredicatesCorrespond resultState.requirements
        ((instantiateLocalSchemePredicates instantiated.substitution
          binder).map (Detail.applyPredicate advanced)) allocation.1
    at branchFacts
  obtain ⟨coercions, recordedContains, actualUnique, actualDisjoint,
      resultCorresponds⟩ := branchFacts
  have evidenceCorresponds :
      RequirementPredicatesCorrespond evidenceState.requirements
        ((instantiateLocalSchemePredicates instantiated.substitution
          binder).map (Detail.applyPredicate advanced)) allocation.1 :=
    resultCorresponds.mono requirementsSubset
  have finalCorresponds :
      RequirementPredicatesCorrespond resources.finalState.requirements
        ((instantiateLocalSchemePredicates instantiated.substitution
          binder).map (Detail.applyPredicate advanced)) allocation.1 := by
    rw [resources.requirements_eq]
    exact evidenceCorresponds
  have occurs : ∀ requirement, requirement ∈ allocation.1 →
      PrimaryRequirementOccursAt finalized.typedSource
        (.expression inferred.id) requirement := by
    intro requirement member
    apply retained recordedContains
    change requirement ∈
      allocation.1 ++ Detail.coercionRequirements coercions
    exact List.mem_append_left _ member
  have allocationInferenceEq : allocated.inference = initial.inference := by
    have projection := congrArg
      (fun pair : ExpressionId × State => pair.2.inference) allocationEq
    change initial.inference = allocated.inference at projection
    exact projection.symm
  have finalExtendsAdvanced :
      finalized.substitution.SemanticallyExtends
        advanced.inference.substitution := by
    simpa [advanced, inference, allocationInferenceEq] using
      invariant.substitutionExtension
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have requirements :=
    localReferenceRequirementSequenceProves_afterSemanticExtension
      (finalState := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      (active := active) (source := finalized.typedSource)
      (occurrence := .expression inferred.id)
      (by simpa only [finalSubstitutionEq] using finalExtendsAdvanced)
      finalCorresponds resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered occurs
  have allocatedInvariant :=
    (invariant.allocateExpressionId allocationEq).active
  have environment := localReferenceEnvironmentFacts_of_lookupBinder?
    allocatedInvariant.aligned allocatedInvariant.formation lookupEq
  have appliedDisjoint : ∀ requirement,
      requirement ∈ allocation.1 →
        requirement ∉
          localSchemeTemplateIds
            (binder.applySubstitution finalized.substitution) := by
    simpa only
      [FlexibleSubstitution.localSchemeTemplateIds_applySubstitution] using
        actualDisjoint
  have binders := invariant.typeParameterBinders canonical
  have range := resources.substitutionRangeAdmissible binders
    invariant.signatures_eq_whole invariant.typeParametersEq
    invariant.declarationEq invariant.residual
  have instantiationValid :=
    canonicalLocalSchemeInstantiationValid_afterSubstitution binders
      invariant.residual range environment.2.2.2 environment.2.2.1
      noCapture instantiationStart actualUnique appliedDisjoint
      (by simpa only [finalSubstitutionEq] using requirements)
  have referenceValid : ReferenceUseValid active (.local binder.id)
      (finalized.substitution.apply instantiated.body) allocation.1 := by
    simpa only [FlexibleSubstitution.applyTypedBinder_id] using
      (ReferenceUseValid.local environment.1 environment.2.1
        instantiationValid)
  have rawEndpointEq :
      finalized.substitution.apply
          (advanced.resolve instantiated.body) =
        finalized.substitution.apply instantiated.body := by
    simpa [State.resolve, TypeSystem.InferState.resolve] using
      finalExtendsAdvanced instantiated.body
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.reference name.value (.local binder.id)
        ).applySubstitution finalized.substitution)
      (finalized.substitution.apply
        (advanced.resolve instantiated.body))
      (.ordinary allocation.1) := by
    rw [rawEndpointEq]
    simpa [ExpressionForm.applySubstitution,
      ReferenceResolution.applySubstitution] using
        (ExpressionFormHasRawType.reference (source := semanticSource)
          referenceValid)
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply
        (advanced.resolve instantiated.body)) := by
    rw [rawEndpointEq]
    exact instantiationValid.type_admissible
  have requirementsSubsetFinal : resultState.requirements ⊆
      resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirementsSubset member
  have activeSignaturesEq : active.signatures =
      inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_in_active
      (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      recorded
      (by simpa only [finalSubstitutionEq] using resultSubstitutionExtension)
      requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      traitSuccess profileSuccess activeCatalog activeSignaturesEq traitName
      resources.solve_success resources.solved_context_eq resources.ledger
      resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered)

/-- A resolved proxy annotation is rigidly formed and therefore fixed by the
whole inference substitution.  Its branch closes in the active recursive
context without a source-side context-closure certificate. -/
theorem inferExprFuel_success_proxy_expressionTypingBase_retained_in_active
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    {fuel : Nat} {expression : Syntax.Expr} {marker : Syntax.SourceSpan}
    {sourceType : Syntax.TypeExpr} {expected : Option Ty}
    {initial allocated resultState : State} {id : ExpressionId}
    {inferred : InferredExpression}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (expressionEq : expression.value = .proxy marker sourceType)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (fun row => row.name) =
        some "Coerce")
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  obtain ⟨inner, resolution, recorded⟩ :=
    Detail.inferExprFuel_success_proxy_facts expressionEq allocationEq success
  have canonicalInference : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters := by
    simpa [ownerEq, parametersEq] using canonical
  have activeSignaturesEq : active.signatures =
      inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeParametersEq : active.typeParameters =
      inferenceContext.typeParameters :=
    invariant.typeParametersEq.trans parametersEq.symm
  have activeOwnerEq : active.currentDeclaration =
      some inferenceContext.scope.genericOwner := by
    simpa [ownerEq] using invariant.declarationEq
  have innerWellFormed : TypeWellFormed active inner :=
    resolveSourceType_success_typeWellFormed canonicalInference
      activeSignaturesEq activeParametersEq activeOwnerEq resolution
  have fixedInner : finalized.substitution.apply inner = inner :=
    Detail.resolveSourceType_success_apply_eq_self finalized.substitution
      resolution
  have innerAdmissible : TypeAdmissible active
      (finalized.substitution.apply inner) := by
    rw [fixedInner]
    exact TypeAdmissible.ofWellFormed innerWellFormed
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.proxy inner).applySubstitution
        finalized.substitution)
      (finalized.substitution.apply (.proxy inner)) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution, fixedInner] using
      ExpressionFormHasRawType.proxy innerAdmissible
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply (.proxy inner)) := by
    simpa [fixedInner] using TypeAdmissible.proxy innerAdmissible
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have requirementsSubsetFinal : resultState.requirements ⊆
      resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirementsSubset member
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_in_active
      (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      recorded
      (by simpa only [finalSubstitutionEq] using resultSubstitutionExtension)
      requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      traitSuccess profileSuccess activeCatalog activeSignaturesEq traitName
      resources.solve_success resources.solved_context_eq resources.ledger
      resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered)

/-- Strong recursive expression obligation.  Its conclusion is intentionally
an `ExpressionTypingBase`: a selected enclosing call/operator may rewrite a
child root's authoritative type while retaining its form, requirements, and
direct children.  Closing the base to `ExpressionHasType` is reserved for the
local-source wrapper below, where exact source extension is available. -/
def InferExprFuelRetainedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context},
    Detail.inferExprFuel fuel inferenceContext expression expected initial =
        .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
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
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next) →
    TypingSourceExtends semanticSource finalized.typedSource →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionDirectChildrenRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.expression inferred.id) →
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      semanticContext finalized.substitution inferred

/-- Statement-facing local-source expression theorem.  The raw result source
is an exact prefix of the whole evidence state for statement children; the
substituted result is an exact prefix of `semanticSource`, so the retained
base can be closed to ordinary declarative expression typing there. -/
def InferExprFuelScopedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context},
    Detail.inferExprFuel fuel inferenceContext expression expected initial =
        .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
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
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next) →
    TypingSourceExtends
      ((resultState.toTypedSource roots).applySubstitution
        finalized.substitution) semanticSource →
    TypingSourceExtends semanticSource finalized.typedSource →
    TypingSourceExtends (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.expression inferred.id) →
    ExpressionHasType semanticSource semanticContext inferred.id
      (finalized.substitution.apply inferred.type)

/-- Exact local-source typing is the closure of retained recursive soundness.
This theorem is the stable bridge consumed by statement branches. -/
theorem inferExprFuelScopedSoundness_of_retainedSoundness
    {fuel : Nat}
    (retainedSound : InferExprFuelRetainedSoundness fuel) :
    InferExprFuelScopedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expression expected initial
    resultState evidenceState inferred roots finalized semanticSource
    semanticContext success resources resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant expectedBelow
    resultExtension semanticExtension rawExtension integerPatternsSubset
    integerLiteralsSubset requirementsSubset covered
  have resultToFinal : TypingSourceExtends
      ((resultState.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource :=
    TypingSourceExtends.trans resultExtension semanticExtension
  have requirementsRetained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id :=
    ExpressionRequirementsRetainedAt.ofTypingSourceExtends
      finalized.substitution resultToFinal
  have childrenRetained : ExpressionDirectChildrenRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id :=
    ExpressionDirectChildrenRetainedAt.ofTypingSourceExtends
      finalized.substitution resultToFinal
  have base := retainedSound success resources resultSubstitutionExtension
    signaturesEq ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant expectedBelow semanticExtension
    integerPatternsSubset integerLiteralsSubset requirementsSubset
    requirementsRetained childrenRetained covered
  cases base with
  | @intro node rawType plan contains typeEq formType rawAdmissible
      requirements =>
      have evidenceMember : Node.expression node ∈
          (evidenceState.toTypedSource roots).nodes :=
        rawExtension.nodes_prefix.subset contains.1
      have finalAdmissible : TypeAdmissible semanticContext
          (finalized.substitution.apply inferred.type) := by
        have nodeAdmissible := resources.expressionTypeAdmissible_in_active
          evidenceMember
          (invariant.typeParameterBinders (by
            simpa [ownerEq, typeParametersEq] using canonical))
          invariant.signatures_eq_whole invariant.typeParametersEq
          invariant.declarationEq invariant.residual
        simpa only [typeEq] using nodeAdmissible
      exact
        (ExpressionTypingBase.intro contains typeEq formType rawAdmissible
          requirements).expressionHasType
          (ExpressionNodesPreservedAt.ofTypingSourceExtends resultExtension)
          finalAdmissible

end Solcore.SourceSemantics.SourceInferenceSoundness
end
