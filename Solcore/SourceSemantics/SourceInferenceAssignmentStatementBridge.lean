import Solcore.SourceSemantics.SourceInferenceAssignmentRecursiveSoundness

/-!
The assignment branches of statement inference delegate to place and
expression inference.  This bridge discharges the branch-local child-typing
callback with the *actual* successful assignment traversal, in the final
parent statement source.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- The value-assignment statement is well typed when the actual delegated
place and expression traversals satisfy their recursive soundness contracts. -/
theorem inferStatementFuel_success_assignValue_recursive_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {targetExpression value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext}
    (statementEq : statement.value =
      .assignValue targetExpression operator value)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈ inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (ready : initial.InferenceReady)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (invariant : ActiveLocalContextInvariant initial finalized.substitution
      semanticContext)
    (allocatedInvariant : RecursiveExpressionInvariant wholeContext finalized
      allocated semanticContext)
    (outerExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (closed : OccurrenceGraphClosed finalized.typedSource)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (parentToEvidence : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (resultIntegerPatternsSubset :
      result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (resultIntegerLiteralsSubset :
      result.state.integerLiterals ⊆ evidenceState.integerLiterals)
    (resultRequirementsSubset :
      result.state.requirements ⊆ evidenceState.requirements)
    (placeSound : InferPlaceFuelScopedSoundness fuel)
    (expressionSound : InferExprFuelScopedSoundness fuel) :
    ActiveLocalContextInvariant result.state finalized.substitution
        semanticContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        control semanticContext result.id semanticContext {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } := by
  apply inferStatementFuel_success_assignValue_bounded_scoped
    statementEq allocationEq success ready initialBelow signatureFormation
    functionsCanonical invariant outerExtension roots parentCovered closed
    resultExtension resultIntegerPatternsSubset resultIntegerLiteralsSubset
    resultRequirementsSubset
  intro assignment inferred assignmentState assignmentSuccess
    _assignmentExtension assignmentPatternsSubset assignmentLiteralsSubset
    assignmentRequirementsSubset keysCovered rhsCovered
  obtain ⟨actualAssignment, actualInferred, actualState, actualSuccess,
      resultEq, _⟩ :=
    inferStatementFuel_success_assignValue_facts statementEq allocationEq
      success roots
  rw [assignmentSuccess] at actualSuccess
  obtain ⟨rfl, rfl, rfl⟩ := (Except.ok.inj actualSuccess).symm
  have assignmentToParent : TypingSourceExtends
      (assignmentState.toTypedSource roots)
      (result.state.toTypedSource roots) := by
    rw [resultEq]
    constructor
    · rfl
    · exact State.recordNode_nodesPrefix assignmentState _
  have assignmentSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        assignmentState.inference.substitution := by
    rw [resultEq] at outerExtension
    simpa [State.recordNode] using outerExtension
  exact inferAssignedValueFuel_children_scopedSound assignmentSuccess
    resources signaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical catalog signatureParameters
    allocatedInvariant assignmentSubstitutionExtension assignmentToParent
    parentToEvidence resultExtension assignmentPatternsSubset
    assignmentLiteralsSubset assignmentRequirementsSubset keysCovered
    rhsCovered placeSound expressionSound

/-- Bit-not assignment traverses an actual place, then unifies its type with
`Word`.  The place's indexed keys are typed before that final unification. -/
theorem inferStatementFuel_success_assignBitNot_recursive_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {targetExpression : Syntax.Expr}
    {operatorSpan : Syntax.SourceSpan}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext}
    (statementEq : statement.value =
      .assignBitNot targetExpression operatorSpan)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈ inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (invariant : ActiveLocalContextInvariant initial finalized.substitution
      semanticContext)
    (allocatedInvariant : RecursiveExpressionInvariant wholeContext finalized
      allocated semanticContext)
    (outerExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (closed : OccurrenceGraphClosed finalized.typedSource)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (parentToEvidence : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (resultIntegerPatternsSubset :
      result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (resultIntegerLiteralsSubset :
      result.state.integerLiterals ⊆ evidenceState.integerLiterals)
    (resultRequirementsSubset :
      result.state.requirements ⊆ evidenceState.requirements)
    (placeSound : InferPlaceFuelScopedSoundness fuel) :
    ActiveLocalContextInvariant result.state finalized.substitution
        semanticContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        control semanticContext result.id semanticContext {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } := by
  apply inferStatementFuel_success_assignBitNot_bounded_scoped
    statementEq allocationEq success initialBelow invariant outerExtension
    roots parentCovered closed resultExtension resultIntegerPatternsSubset
    resultIntegerLiteralsSubset resultRequirementsSubset
  intro place placeState placeSuccess _placeExtension placePatternsSubset
    placeLiteralsSubset placeRequirementsSubset keysCovered
  obtain ⟨actualPlace, actualState, unified, actualSuccess,
      unifySuccess, _, resultEq, _⟩ :=
    inferStatementFuel_success_assignBitNot_facts statementEq allocationEq
      success roots
  rw [placeSuccess] at actualSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualSuccess).symm
  have placeToUnified : TypingSourceExtends
      (placeState.toTypedSource roots) (unified.toTypedSource roots) := by
    constructor
    · have headerEq := Detail.unify_state_header unifySuccess
      have ownerEq := congrArg State.Header.owner headerEq
      simpa [State.toTypedSource, State.header] using ownerEq
    · have nodesEq := (Detail.unify_occurrenceState_eq unifySuccess).1
      change placeState.nodes <+: unified.nodes
      rw [nodesEq]
      exact List.prefix_rfl
  have unifiedToParent : TypingSourceExtends
      (unified.toTypedSource roots)
      (result.state.toTypedSource roots) := by
    rw [resultEq]
    constructor
    · rfl
    · exact State.recordNode_nodesPrefix unified _
  have placeToParent := placeToUnified.trans unifiedToParent
  have unifiedSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        unified.inference.substitution := by
    rw [resultEq] at outerExtension
    simpa [State.recordNode] using outerExtension
  have placeProperties := Detail.inferPlaceFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical
    placeSuccess
  have unifyProgress := Detail.unify_inferenceProgress
    placeProperties.2.1.solved placeProperties.2.2
    (Ty.variablesBelow_constructor _ _) unifySuccess
  have placeSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        placeState.inference.substitution :=
    Substitution.SemanticallyExtends.trans unifiedSubstitutionExtension
      unifyProgress.substitution_extends
  exact placeSound placeSuccess resources signaturesEq ownerEq parametersEq
    assumptionsEq signatureFormation functionsCanonical catalog
    signatureParameters allocatedInvariant placeSubstitutionExtension
    placeToParent parentToEvidence placePatternsSubset placeLiteralsSubset
    placeRequirementsSubset keysCovered

end Solcore.SourceSemantics.SourceInferenceSoundness
