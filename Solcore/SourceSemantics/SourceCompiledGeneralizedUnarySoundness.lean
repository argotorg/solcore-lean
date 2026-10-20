import Solcore.SourceSemantics.SourceCompiledProvenanceExpressionContracts
import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedNamedCall
import Solcore.SourceSemantics.SourceInferenceSelectedOperatorRecording

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

theorem expressionRetained_unary_operator_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundnessFor provenance selected childFuel)
    {inferenceContext : SourceInference.Context} {expression operandExpression : Syntax.Expr}
    {operator : Syntax.Located Syntax.UnaryOp} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target)
    {allocated operandState : State} {id : ExpressionId}
    {operand : InferredExpression} {operatorResult : Detail.OperatorInferenceResult}
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (operandSuccess : Detail.inferExprFuel childFuel inferenceContext operandExpression none allocated =
      .ok (operand, operandState))
    (operandHere : provenance (.expression childFuel inferenceContext operandExpression none
      allocated operand operandState))
    (operatorSuccess : Detail.inferUnaryOperator inferenceContext operator.value operand.type expected
      (Detail.relevantIntegerLiterals operandState allocated.integerLiterals.length [operand])
      operandState = .ok operatorResult)
    (recorded : Detail.recordExpressionWithExpected inferenceContext expression id operatorResult.type
      (.unary operator.value operand.id) operatorResult.requirements expected
      operatorResult.state = .ok (inferred, resultState)) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  let wholeContext := checkingContext selected
  let finalized := selected.body.finalized
  let roots := bodyRoots selected
  let evidenceState := selected.body.returned
  let semanticSource := selected.body.finalized.typedSource
  let semanticContext := target
  have resources := selected.body.resources
  have interfaces := boundary.interfaces
  have resultSubstitutionExtension := boundary.extension
  have signaturesEq := boundary.scope.signatures
  have ownerEq := boundary.scope.owner
  have typeParametersEq := boundary.scope.parameters
  have signatureFormation := boundary.scope.formation checked
  have functionsCanonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  have canonical := boundary.scope.canonical checked
  have integerPatternsSubset := boundary.integerPatterns
  have integerLiteralsSubset := boundary.integerLiterals
  have requirementsSubset := boundary.requirements
  have covered := boundary.covered
  have invariant := boundary.invariant
  have expectedBelow := boundary.expectedBelow
  have success := boundary.accepted
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational : GeneralizedActualStateInvariant allocated (evidenceSource selected) := by
    rw [← show initial.allocateExpressionId.2 = allocated from congrArg Prod.snd allocationEq]
    exact boundary.operational.allocateExpressionId
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
  have finalEdge := boundary.directChildren edge
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
  have typed := expressionRooted_of_retained_for checked recursive operandHere ({
    accepted := operandSuccess
    interfaces := boundary.interfaces
    extension := childExtension
    scope := boundary.scope
    invariant := allocatedInvariant
    actual := boundary.actual
    operational := allocatedOperational
    expectedBelow := by simp
    expectedAdmissible := by simp
    expectedSafe := by simp
    integerPatterns := childPatterns
    integerLiterals := childLiterals
    requirements := childRequirements
    covered := boundary.covered.expressionChild resources.graph_closed finalEdge
    actualCovered := boundary.actualCovered.directChild finalEdge
    rawSubtree := (boundary.rawProper.childSubtree edge).monoBefore childToParent } :
    RootedExpressionBoundary selected childFuel inferenceContext operandExpression none
      allocated operand operandState frames target)
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
      finalRequirements boundary.expressionRequirements (by simpa only [signaturesEq] using interfaces) boundary.coercionPrimaries boundary.operatorSite
      activeCatalog (invariant.typeParameterBinders wholeCanonical) activeSignatures
      resources.solve_success resources.solved_context_eq resources.ledger resources.ownership
      invariant.signaturesEq invariant.solvedRequirementsEq invariant.assumptionsMono covered)

theorem expressionRetained_unary_operator
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression operandExpression : Syntax.Expr}
    {operator : Syntax.Located Syntax.UnaryOp} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target)
    {allocated operandState : State} {id : ExpressionId}
    {operand : InferredExpression} {operatorResult : Detail.OperatorInferenceResult}
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (operandSuccess : Detail.inferExprFuel childFuel inferenceContext operandExpression none allocated =
      .ok (operand, operandState))
    (operatorSuccess : Detail.inferUnaryOperator inferenceContext operator.value operand.type expected
      (Detail.relevantIntegerLiterals operandState allocated.integerLiterals.length [operand])
      operandState = .ok operatorResult)
    (recorded : Detail.recordExpressionWithExpected inferenceContext expression id operatorResult.type
      (.unary operator.value operand.id) operatorResult.requirements expected
      operatorResult.state = .ok (inferred, resultState)) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  exact expressionRetained_unary_operator_for (provenance := fun _ => True) checked
    (fun _ boundary => recursive boundary) boundary allocationEq operandSuccess trivial
    operatorSuccess recorded

theorem expressionRetained_unary_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed provenance)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor provenance selected smaller)
    {inferenceContext : SourceInference.Context} {expression operandExpression : Syntax.Expr}
    {operator : Syntax.Located Syntax.UnaryOp} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : provenance (.expression (childFuel + 1) inferenceContext expression expected
      initial inferred resultState))
    (expressionEq : expression.value = .unary operator operandExpression)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  generalize allocationEq : initial.allocateExpressionId = pair
  obtain ⟨id, allocated⟩ := pair
  obtain ⟨operand, operandState, operandSuccess, dispatch⟩ :=
    Detail.inferExprFuel_success_unary_facts expressionEq allocationEq boundary.accepted
  have operandHere := descend here
    (ChildStep.expression_unary boundary.accepted expressionEq allocationEq operandSuccess)
  cases dispatch with
  | directFunction _ _ operatorSuccess recorded =>
      exact expressionRetained_unary_operator_for checked (recursive childFuel (Nat.lt_succ_self _))
        boundary allocationEq operandSuccess operandHere operatorSuccess recorded
  | traitMethod _ operatorSuccess recorded =>
      exact expressionRetained_unary_operator_for checked (recursive childFuel (Nat.lt_succ_self _))
        boundary allocationEq operandSuccess operandHere operatorSuccess recorded
  | selectedFunction _ lookup selectedCall recorded =>
      have argumentCalls := OrderedExpressionCalls.singleton operandSuccess operandHere
      have argumentsSuccess := argumentCalls.accepted
      have allocatedOperational : GeneralizedActualStateInvariant allocated (evidenceSource selected) := by
        rw [← show initial.allocateExpressionId.2 = allocated from congrArg Prod.snd allocationEq]
        exact boundary.operational.allocateExpressionId
      exact selectedCall_typing_for checked recursive boundary
        (boundary.invariant.allocateExpressionId allocationEq) allocatedOperational
        (by simpa only [allocateExpressionId_inferenceNext_eq allocationEq] using boundary.expectedBelow)
        argumentCalls argumentsSuccess selectedCall recorded (Detail.functionsNamed_success_subset_catalog lookup)

theorem expressionRetained_unary
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {expression operandExpression : Syntax.Expr}
    {operator : Syntax.Located Syntax.UnaryOp} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (expressionEq : expression.value = .unary operator operandExpression)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  exact expressionRetained_unary_for (provenance := fun _ => True) checked true_childClosed
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursive smaller less boundary) trivial expressionEq boundary
end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
