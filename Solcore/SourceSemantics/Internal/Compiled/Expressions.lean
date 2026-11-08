import Solcore.SourceSemantics.Internal.Compiled.Contracts
import Solcore.SourceSemantics.Internal.Compiled.BodySelection
import Solcore.SourceSemantics.Internal.Compiled.Calls
import Solcore.SourceSemantics.Internal.Selected.Operators
import Solcore.SourceSemantics.Internal.Selected.ExpressionSoundness
import Solcore.SourceSemantics.Internal.Compiled.OperationalState
import Solcore.SourceSemantics.Internal.Inference.ExpressionRetained
import Solcore.SourceSemantics.Internal.Compiled.LoopHeaders
import Solcore.SourceSemantics.Internal.Compiled.InitializerOccurrences
import Solcore.SourceSemantics.Internal.Selected.State
import Solcore.SourceSemantics.Internal.Selected.Children
import Solcore.SourceSemantics.Internal.Compiled.AtomicExpressions

/-!
# Typing of generalized expressions

Unary, binary, constructor, conditional, index and lambda expressions, the expression dispatch and
the place contracts, all over one selected final source.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedUnarySoundness
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedBinarySoundness
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

theorem expressionRetained_binary_operator_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundnessFor provenance selected childFuel)
    {inferenceContext : SourceInference.Context} {expression leftExpression rightExpression : Syntax.Expr}
    {operator : Syntax.Located Syntax.BinaryOp} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target)
    {allocated leftState rightState : State} {id : ExpressionId}
    {left right : InferredExpression}
    {operatorResult : Detail.OperatorInferenceResult}
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (leftSuccess : Detail.inferExprFuel childFuel inferenceContext leftExpression none allocated = .ok (left, leftState))
    (rightSuccess : Detail.inferExprFuel childFuel inferenceContext rightExpression none leftState = .ok (right, rightState))
    (leftHere : provenance (.expression childFuel inferenceContext leftExpression none
      allocated left leftState))
    (rightHere : provenance (.expression childFuel inferenceContext rightExpression none
      leftState right rightState))
    (operatorSuccess : Detail.inferBinaryOperator inferenceContext operator.value left.type right.type expected
      (Detail.relevantIntegerLiterals rightState allocated.integerLiterals.length [left, right])
      rightState = .ok operatorResult)
    (recorded : Detail.recordExpressionWithExpected inferenceContext expression id operatorResult.type
      (.binary left.id operator.value right.id) operatorResult.requirements expected
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
  have finalPreserved := boundary.proper
  have semanticPreserved := boundary.proper
  have rawProper := boundary.rawProper
  have actualCovered := boundary.actualCovered
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational : GeneralizedActualStateInvariant allocated (evidenceSource selected) := by
    rw [← show initial.allocateExpressionId.2 = allocated from congrArg Prod.snd allocationEq]
    exact boundary.operational.allocateExpressionId
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
  have leftTyped := expressionRooted_of_retained_for checked recursive leftHere ({
    accepted := leftSuccess
    interfaces := boundary.interfaces
    extension := leftExtension
    scope := boundary.scope
    invariant := allocatedInvariant
    actual := boundary.actual
    operational := allocatedOperational
    expectedBelow := by simp
    expectedAdmissible := by simp
    expectedSafe := by simp
    integerPatterns := ((Detail.inferExprFuel_integerPatterns_subset rightSuccess).trans rightPatterns)
    integerLiterals := ((Detail.inferExprFuel_integerLiterals_subset rightSuccess).trans rightLiterals)
    requirements := ((Detail.inferExprFuel_requirements_subset rightSuccess).trans rightRequirements)
    covered := covered.expressionChild resources.graph_closed (boundary.directChildren leftEdge)
    actualCovered := actualCovered.directChild (boundary.directChildren leftEdge)
    rawSubtree := (rawProper.childSubtree leftEdge).monoBefore leftToParent } : RootedExpressionBoundary _ _ _ _ _ _ _ _ _ _)
  have leftInvariant := allocatedInvariant.ofExpression signatureFormation functionsCanonical (by simp) leftExtension leftSuccess
  have leftOperational := allocatedOperational.ofExpression allocatedInvariant.ready catalog
    signatureFormation functionsCanonical (by simp) (by simp) leftSuccess
  have rightTyped := expressionRooted_of_retained_for checked recursive rightHere ({
    accepted := rightSuccess
    interfaces := boundary.interfaces
    extension := rightExtension
    scope := boundary.scope
    invariant := leftInvariant
    actual := boundary.actual
    operational := leftOperational
    expectedBelow := by simp
    expectedAdmissible := by simp
    expectedSafe := by simp
    integerPatterns := rightPatterns
    integerLiterals := rightLiterals
    requirements := rightRequirements
    covered := covered.expressionChild resources.graph_closed (boundary.directChildren rightEdge)
    actualCovered := actualCovered.directChild (boundary.directChildren rightEdge)
    rawSubtree := (rawProper.childSubtree rightEdge).monoBefore rightToParent } : RootedExpressionBoundary _ _ _ _ _ _ _ _ _ _)
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
      finalRequirements boundary.expressionRequirements (by simpa only [signaturesEq] using interfaces) boundary.coercionPrimaries boundary.operatorSite
      activeCatalog (invariant.typeParameterBinders wholeCanonical) activeSignatures
      resources.solve_success resources.solved_context_eq resources.ledger resources.ownership
      invariant.signaturesEq invariant.solvedRequirementsEq invariant.assumptionsMono covered)

theorem expressionRetained_binary_operator
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression leftExpression rightExpression : Syntax.Expr}
    {operator : Syntax.Located Syntax.BinaryOp} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target)
    {allocated leftState rightState : State} {id : ExpressionId}
    {left right : InferredExpression}
    {operatorResult : Detail.OperatorInferenceResult}
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (leftSuccess : Detail.inferExprFuel childFuel inferenceContext leftExpression none allocated = .ok (left, leftState))
    (rightSuccess : Detail.inferExprFuel childFuel inferenceContext rightExpression none leftState = .ok (right, rightState))
    (operatorSuccess : Detail.inferBinaryOperator inferenceContext operator.value left.type right.type expected
      (Detail.relevantIntegerLiterals rightState allocated.integerLiterals.length [left, right])
      rightState = .ok operatorResult)
    (recorded : Detail.recordExpressionWithExpected inferenceContext expression id operatorResult.type
      (.binary left.id operator.value right.id) operatorResult.requirements expected
      operatorResult.state = .ok (inferred, resultState)) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  exact expressionRetained_binary_operator_for (provenance := fun _ => True) checked
    (fun _ boundary => recursive boundary) boundary allocationEq leftSuccess rightSuccess
    trivial trivial operatorSuccess recorded

theorem expressionRetained_binary_selected_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundnessFor provenance selected childFuel)
    {inferenceContext : SourceInference.Context} {expression leftExpression rightExpression : Syntax.Expr}
    {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target)
    {allocated leftState rightState : State} {id : ExpressionId}
    {left right : InferredExpression}
    {name : String} {candidates : List ProgramFunctionSignature}
    {attempt : Detail.CandidateAttemptResult} {fitted : Detail.ExpectationResult} {callee : Syntax.Expr}
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (leftSuccess : Detail.inferExprFuel childFuel inferenceContext leftExpression none allocated = .ok (left, leftState))
    (rightSuccess : Detail.inferExprFuel childFuel inferenceContext rightExpression none leftState = .ok (right, rightState))
    (leftHere : provenance (.expression childFuel inferenceContext leftExpression none
      allocated left leftState))
    (rightHere : provenance (.expression childFuel inferenceContext rightExpression none
      leftState right rightState))
    (selectionSuccess : Detail.selectFunctionCandidateFrom inferenceContext name candidates [left, right]
      (Detail.relevantIntegerLiterals rightState allocated.integerLiterals.length [left, right])
      id (some .bool) rightState = .ok attempt)
    (fitting : Detail.withExpected inferenceContext attempt.state attempt.result expected = .ok fitted)
    (recordSuccess : Detail.recordSelectedCallResult expression callee name [left, right] attempt
      fitted.expression fitted.coercions fitted.state = (inferred, resultState))
    (candidatesSubset : candidates ⊆ inferenceContext.signatures.functions) :
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
  have finalPreserved := boundary.proper
  have semanticPreserved := boundary.proper
  have rawProper := boundary.rawProper
  have actualCovered := boundary.actualCovered
  have inferredEq : inferred = fitted.expression := (Detail.recordSelectedCallResult_success_nodes recordSuccess).1
  subst inferred
  have resultIdEq := Detail.withExpected_success_expression_id fitting
  have activeSignaturesEq := invariant.signatures_eq_whole.trans signaturesEq.symm
  obtain ⟨signature, _, signatureMember, signatureCanonical, schemeBelow, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_semanticCandidate signatureFormation functionsCanonical
      activeSignaturesEq candidatesSubset selectionSuccess
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational : GeneralizedActualStateInvariant allocated (evidenceSource selected) := by
    rw [← show initial.allocateExpressionId.2 = allocated from congrArg Prod.snd allocationEq]
    exact boundary.operational.allocateExpressionId
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
      boundary.directChildren resources.graph_closed entry entryMember).monoBefore rightToFitted
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
  have leftTyped := recursive leftHere ({
    accepted := leftSuccess
    interfaces := boundary.interfaces
    extension := leftExtension
    scope := boundary.scope
    invariant := allocatedInvariant
    actual := boundary.actual
    operational := allocatedOperational
    expectedBelow := by simp
    expectedAdmissible := by simp
    expectedSafe := by simp
    integerPatterns := ((Detail.inferExprFuel_integerPatterns_subset rightSuccess).trans rightPatterns)
    integerLiterals := ((Detail.inferExprFuel_integerLiterals_subset rightSuccess).trans rightLiterals)
    requirements := ((Detail.inferExprFuel_requirements_subset rightSuccess).trans rightRequirements)
    covered := covered.expressionChild resources.graph_closed (boundary.directChildren (argumentEdge left (by simp)))
    actualCovered := actualCovered.directChild (boundary.directChildren (argumentEdge left (by simp)))
    proper := leftPreserved.finalized
    rawProper := leftPreserved.raw
    expressionRequirements := leftPreserved.requirements
    coercionPrimaries := leftPreserved.coercions
    operatorSite := leftPreserved.operators
    directChildren := leftPreserved.children } : RetainedExpressionBoundary _ _ _ _ _ _ _ _ _ _)
  have leftInvariant := allocatedInvariant.ofExpression signatureFormation functionsCanonical (by simp) leftExtension leftSuccess
  have leftOperational := allocatedOperational.ofExpression allocatedInvariant.ready catalog
    signatureFormation functionsCanonical (by simp) (by simp) leftSuccess
  have rightPreserved := argumentPreserved right (by simp)
  have rightTyped := recursive rightHere ({
    accepted := rightSuccess
    interfaces := boundary.interfaces
    extension := rightExtension
    scope := boundary.scope
    invariant := leftInvariant
    actual := boundary.actual
    operational := leftOperational
    expectedBelow := by simp
    expectedAdmissible := by simp
    expectedSafe := by simp
    integerPatterns := rightPatterns
    integerLiterals := rightLiterals
    requirements := rightRequirements
    covered := covered.expressionChild resources.graph_closed (boundary.directChildren (argumentEdge right (by simp)))
    actualCovered := actualCovered.directChild (boundary.directChildren (argumentEdge right (by simp)))
    proper := rightPreserved.finalized
    rawProper := rightPreserved.raw
    expressionRequirements := rightPreserved.requirements
    coercionPrimaries := rightPreserved.coercions
    operatorSite := rightPreserved.operators
    directChildren := rightPreserved.children } : RetainedExpressionBoundary _ _ _ _ _ _ _ _ _ _)
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
    obtain ⟨node, found, finalStep, site, same⟩ := boundary.coercionPrimaries callContains step
      (List.mem_append_left _ (List.mem_append_right _ member))
    exact ⟨node, found.1, finalStep, site, same⟩
  have occurs : ∀ requirement ∈ coercionRequirementIds fitted.coercions,
      PrimaryRequirementOccursAt finalized.typedSource (.expression fitted.expression.id) requirement := by
    intro requirement member
    apply boundary.expressionRequirements callContains
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
      boundary.expressionRequirements (by simpa only [signaturesEq] using interfaces) boundary.coercionPrimaries
      (fun entry member => covered.expressionChild resources.graph_closed (boundary.directChildren (entryEdge entry member)))
      activeCatalog binders invariant.residual (by simpa only [finalSubstitutionEq] using range)
      signatureMember activeSignaturesEq resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership invariant.signaturesEq invariant.solvedRequirementsEq
      invariant.assumptionsMono covered trailing)

theorem expressionRetained_binary_selected
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression leftExpression rightExpression : Syntax.Expr}
    {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target)
    {allocated leftState rightState : State} {id : ExpressionId}
    {left right : InferredExpression}
    {name : String} {candidates : List ProgramFunctionSignature}
    {attempt : Detail.CandidateAttemptResult} {fitted : Detail.ExpectationResult} {callee : Syntax.Expr}
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (leftSuccess : Detail.inferExprFuel childFuel inferenceContext leftExpression none allocated = .ok (left, leftState))
    (rightSuccess : Detail.inferExprFuel childFuel inferenceContext rightExpression none leftState = .ok (right, rightState))
    (selectionSuccess : Detail.selectFunctionCandidateFrom inferenceContext name candidates [left, right]
      (Detail.relevantIntegerLiterals rightState allocated.integerLiterals.length [left, right])
      id (some .bool) rightState = .ok attempt)
    (fitting : Detail.withExpected inferenceContext attempt.state attempt.result expected = .ok fitted)
    (recordSuccess : Detail.recordSelectedCallResult expression callee name [left, right] attempt
      fitted.expression fitted.coercions fitted.state = (inferred, resultState))
    (candidatesSubset : candidates ⊆ inferenceContext.signatures.functions) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  exact expressionRetained_binary_selected_for (provenance := fun _ => True) checked
    (fun _ boundary => recursive boundary) boundary allocationEq leftSuccess rightSuccess
    trivial trivial selectionSuccess fitting recordSuccess candidatesSubset

theorem expressionRetained_binary_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed provenance)
    (recursive : ExpressionRetainedSoundnessFor provenance selected childFuel)
    {inferenceContext : SourceInference.Context} {expression leftExpression rightExpression : Syntax.Expr}
    {operator : Syntax.Located Syntax.BinaryOp} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : provenance (.expression (childFuel + 1) inferenceContext expression expected
      initial inferred resultState))
    (expressionEq : expression.value = .binary leftExpression operator rightExpression)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  generalize allocationEq : initial.allocateExpressionId = pair
  obtain ⟨id, allocated⟩ := pair
  obtain ⟨left, leftState, right, rightState, leftSuccess, rightSuccess, dispatch⟩ :=
    Detail.inferExprFuel_success_binary_facts expressionEq allocationEq boundary.accepted
  have leftHere := descend here
    (ChildStep.expression_binary_left boundary.accepted expressionEq allocationEq leftSuccess)
  have rightHere := descend here
    (ChildStep.expression_binary_right boundary.accepted expressionEq allocationEq leftSuccess rightSuccess)
  cases dispatch with
  | directFunction _ _ operatorSuccess recorded =>
      exact expressionRetained_binary_operator_for checked recursive boundary
        allocationEq leftSuccess rightSuccess leftHere rightHere operatorSuccess recorded
  | traitMethod _ operatorSuccess recorded =>
      exact expressionRetained_binary_operator_for checked recursive boundary
        allocationEq leftSuccess rightSuccess leftHere rightHere operatorSuccess recorded
  | selectedFunction _ lookup selectedCall fitted recorded =>
      exact expressionRetained_binary_selected_for checked recursive boundary
        allocationEq leftSuccess rightSuccess leftHere rightHere selectedCall fitted recorded
        (Detail.functionsNamed_success_subset_catalog lookup)

theorem expressionRetained_binary
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression leftExpression rightExpression : Syntax.Expr}
    {operator : Syntax.Located Syntax.BinaryOp} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (expressionEq : expression.value = .binary leftExpression operator rightExpression)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  exact expressionRetained_binary_for (provenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursive boundary) trivial expressionEq boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedConstructorApplication
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

theorem constructorApplicationRetained_for {callProvenance : CallIndex → Prop}
    {rawSource : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram rawSource fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ExpressionRetainedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {arguments : List Syntax.Expr} {instantiation : DataConstructorInstantiation} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.constructorApplication childFuel inferenceContext source id instantiation
      arguments expected initial inferred resultState))
    (success : Detail.inferConstructorApplicationFuel childFuel inferenceContext source id instantiation
      arguments expected initial = .ok (inferred, resultState))
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
      selected.body.finalized.solvedRequirements selected.body.finalized.typedSource)
    (extension : selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution)
    (scope : CheckingScope selected inferenceContext)
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (actual : ActualContext (checkingContext selected) selected.body.finalized frames target)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (payloadBelow : ∀ type ∈ instantiation.payloadTypes, type.VariablesBelow initial.inference.next)
    (resultBelow : instantiation.resultType.VariablesBelow initial.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (payloadSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ instantiation.payloadTypes,
      ProtectedVariables.Safe binder.scheme.quantified initial type)
    (resultSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial instantiation.resultType)
    (expectedSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ expected,
      ProtectedVariables.Safe binder.scheme.quantified initial type)
    (instantiationValid : SourceSemantics.DataConstructorInstantiation.Admissible target
      (instantiation.applySubstitution selected.body.finalized.substitution))
    (raw : RawProperDescendantsPreserved (resultState.toTypedSource (bodyRoots selected))
      (evidenceSource selected) (.expression inferred.id))
    (patterns : resultState.integerPatterns ⊆ selected.body.returned.integerPatterns)
    (literals : resultState.integerLiterals ⊆ selected.body.returned.integerLiterals)
    (requirements : resultState.requirements ⊆ selected.body.returned.requirements)
    (retained : ExpressionRequirementsRetainedAt (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource inferred.id)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource inferred.id)
    (childrenRetained : ExpressionDirectChildrenRetainedAt (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource inferred.id)
    (covered : TemplateScopeCovered selected.body.finalized.typedSource target (.expression inferred.id))
    (actualCovered : ActualContext.Covers selected.body.finalized frames (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  have formation := scope.formation checked
  have functions := scope.functionsCanonical checked
  have catalog := scope.catalog checked
  have canonical := scope.canonical checked
  have activeCatalog : SignatureCatalogWellFormed target.signatures := by
    rw [invariant.signatures_eq_whole, ← scope.signatures]; exact catalog
  have binders := invariant.typeParameterBinders (by simpa only [scope.owner, scope.parameters] using canonical)
  have finish {argumentInitial argumentsState : State} {inferredArguments : List InferredExpression}
      (argumentInvariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized argumentInitial target)
      (argumentOperational : GeneralizedActualStateInvariant argumentInitial (evidenceSource selected))
      (argumentSafe : ∀ binder ∈ argumentInitial.localBinders, ∀ type ∈ instantiation.payloadTypes,
        ProtectedVariables.Safe binder.scheme.quantified argumentInitial type)
      (payloadAt : ∀ type ∈ instantiation.payloadTypes, type.VariablesBelow argumentInitial.inference.next)
      (resultAt : instantiation.resultType.VariablesBelow argumentInitial.inference.next)
      (expectedAt : ∀ type ∈ expected, type.VariablesBelow argumentInitial.inference.next)
      (argumentsHere : callProvenance (.constructorArguments childFuel inferenceContext arguments
        instantiation.payloadTypes argumentInitial inferredArguments argumentsState))
      (argumentsSuccess : Detail.inferConstructorArgumentsFuel childFuel inferenceContext arguments instantiation.payloadTypes
        argumentInitial = .ok (inferredArguments, argumentsState))
      (recorded : Detail.recordExpressionWithExpected inferenceContext source id
        (argumentsState.resolve instantiation.resultType) (.constructor instantiation (inferredArguments.map (·.id))) []
        expected argumentsState = .ok (inferred, resultState)) :
      ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
    have properties := Detail.inferConstructorArgumentsFuel_inferenceProperties argumentInvariant.ready formation functions
      payloadAt argumentsSuccess
    have recording := Detail.recordExpressionWithExpected_inferenceProperties properties.2.1
      (properties.2.1.solved.variablesBelow_apply (resultAt.weaken properties.1.next_le))
      (fun type member => (expectedAt type member).weaken properties.1.next_le) recorded
    have argumentExtension := extension.trans recording.1.substitution_extends
    have argumentToParent : TypingSourceExtends (argumentsState.toTypedSource (bodyRoots selected)) (resultState.toTypedSource (bodyRoots selected)) := by
      constructor
      · obtain ⟨fitted, fittedSuccess, _, stateEq⟩ := Detail.recordExpressionWithExpected_success_record recorded
        change resultState.owner = argumentsState.owner
        dsimp only at stateEq
        rw [stateEq]
        exact congrArg State.Header.owner (Detail.SelectedMetadata.withExpected_state_header fittedSuccess)
      · exact recordExpressionWithExpected_success_nodesPrefix recorded
    obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded (bodyRoots selected)
    have edge : ∀ argument ∈ inferredArguments, DirectChild (resultState.toTypedSource (bodyRoots selected))
        (.expression inferred.id) (.expression argument.id) := by
      intro argument member
      refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
      simp only [nodeChildIds, Node.references, ExpressionForm.references]
      exact List.mem_map.mpr ⟨argument.id, List.mem_map.mpr ⟨argument, member, rfl⟩, rfl⟩
    have payloadAdmissible : ∀ type ∈ instantiation.payloadTypes,
        TypeAdmissible target (selected.body.finalized.substitution.apply type) := by
      intro type member
      apply SourceSemantics.DataConstructorInstantiation.Admissible.payload_type_admissible
        activeCatalog binders instantiationValid
      exact List.mem_map.mpr ⟨type, member, rfl⟩
    have typed := constructorArgumentsRooted_for checked descend recursive argumentsHere argumentsSuccess interfaces argumentExtension
      scope argumentInvariant actual argumentOperational payloadAt payloadAdmissible argumentSafe
      (fun argument member => (raw.childSubtree (edge argument member)).monoBefore argumentToParent)
      (by rw [← recordExpressionWithExpected_integerPatterns_eq recorded]; exact patterns)
      (by rw [← Detail.recordExpressionWithExpected_integerLiterals_eq recorded]; exact literals)
      ((Detail.recordExpressionWithExpected_requirements_subset recorded).trans requirements)
      (fun argument member => covered.expressionChild selected.body.resources.graph_closed (childrenRetained (edge argument member)))
      (fun argument member => actualCovered.directChild (childrenRetained (edge argument member)))
    have rawEq : selected.body.finalized.substitution.apply (argumentsState.resolve instantiation.resultType) =
        selected.body.finalized.substitution.apply instantiation.resultType := by
      simpa only [State.resolve, InferState.resolve] using argumentExtension instantiation.resultType
    have rawAdmissible : TypeAdmissible target
        (selected.body.finalized.substitution.apply (argumentsState.resolve instantiation.resultType)) := by
      rw [rawEq]
      exact SourceSemantics.DataConstructorInstantiation.Admissible.result_type_admissible
        binders instantiationValid
    have formType : ExpressionFormHasRawType selected.body.finalized.typedSource target
        ((.constructor instantiation (inferredArguments.map (·.id)) : ExpressionForm).applySubstitution selected.body.finalized.substitution)
        (selected.body.finalized.substitution.apply (argumentsState.resolve instantiation.resultType)) (.ordinary []) := by
      rw [rawEq]
      exact .constructor instantiationValid typed
    exact recordExpressionWithExpected_success_expressionTypingBase_actual selected.body.resources interfaces recorded extension
      requirements retained coercionsRetained catalog scope.signatures invariant formType rawAdmissible covered
  have parentAccepted := success
  unfold Detail.inferConstructorApplicationFuel at success
  by_cases arity : arguments.length = instantiation.payloadTypes.length
  · simp only [arity] at success
    cases expected with
    | none =>
      simp only [pure, Pure.pure, Except.pure, bind, Except.bind] at success
      cases args : Detail.inferConstructorArgumentsFuel childFuel inferenceContext arguments instantiation.payloadTypes initial with
      | error error => simp [args] at success
      | ok pair =>
        obtain ⟨inferredArguments, argumentsState⟩ := pair
        simp only [args] at success
        exact finish invariant operational payloadSafe payloadBelow resultBelow expectedBelow
          (descend here (.constructorApplication_arguments parentAccepted arity rfl args)) args success
    | some expectedType =>
      cases unified : Detail.unify initial instantiation.resultType expectedType with
      | error error => simp [unified, bind, Except.bind] at success
      | ok argumentInitial =>
        simp only [unified, bind, Except.bind] at success
        have expectedTypeBelow := expectedBelow expectedType (by simp)
        have progress := Detail.unify_inferenceProgress invariant.ready.solved resultBelow expectedTypeBelow unified
        cases args : Detail.inferConstructorArgumentsFuel childFuel inferenceContext arguments instantiation.payloadTypes argumentInitial with
        | error error => simp [args] at success
        | ok pair =>
          obtain ⟨inferredArguments, argumentsState⟩ := pair
          simp only [args] at success
          have argumentReady := Detail.unify_preserves_inferenceReady invariant.ready resultBelow expectedTypeBelow unified
          have argsProperties := Detail.inferConstructorArgumentsFuel_inferenceProperties argumentReady formation functions
            (fun type member => (payloadBelow type member).weaken progress.next_le) args
          have recordProperties := Detail.recordExpressionWithExpected_inferenceProperties argsProperties.2.1
            (argsProperties.2.1.solved.variablesBelow_apply
              (resultBelow.weaken (Nat.le_trans progress.next_le argsProperties.1.next_le)))
            (fun type member => (expectedBelow type member).weaken (Nat.le_trans progress.next_le argsProperties.1.next_le)) success
          have argumentExtension := extension.trans (recordProperties.1.substitution_extends.trans argsProperties.1.substitution_extends)
          exact finish (invariant.unify resultBelow expectedTypeBelow argumentExtension unified)
            (operational.unify invariant.ready resultBelow expectedTypeBelow resultSafe
              (fun binder member => expectedSafe binder member expectedType (by simp)) unified)
            (by
              intro binder member type typeMember
              have same : argumentInitial.localBinders = initial.localBinders :=
                congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unified)
              have old := same ▸ member
              exact ProtectedVariables.unify (resultSafe binder old)
                (expectedSafe binder old expectedType (by simp)) unified type
                (payloadSafe binder old type typeMember))
            (fun type member => (payloadBelow type member).weaken progress.next_le)
            (resultBelow.weaken progress.next_le)
            (fun type member => (expectedBelow type member).weaken progress.next_le)
            (descend here (.constructorApplication_arguments parentAccepted arity unified args)) args success
  · simp [arity, bind, Except.bind] at success


theorem constructorApplicationRetained
    {rawSource : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram rawSource fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {arguments : List Syntax.Expr} {instantiation : DataConstructorInstantiation} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (success : Detail.inferConstructorApplicationFuel childFuel inferenceContext source id instantiation
      arguments expected initial = .ok (inferred, resultState))
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
      selected.body.finalized.solvedRequirements selected.body.finalized.typedSource)
    (extension : selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution)
    (scope : CheckingScope selected inferenceContext)
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (actual : ActualContext (checkingContext selected) selected.body.finalized frames target)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (payloadBelow : ∀ type ∈ instantiation.payloadTypes, type.VariablesBelow initial.inference.next)
    (resultBelow : instantiation.resultType.VariablesBelow initial.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (payloadSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ instantiation.payloadTypes,
      ProtectedVariables.Safe binder.scheme.quantified initial type)
    (resultSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial instantiation.resultType)
    (expectedSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ expected,
      ProtectedVariables.Safe binder.scheme.quantified initial type)
    (instantiationValid : SourceSemantics.DataConstructorInstantiation.Admissible target
      (instantiation.applySubstitution selected.body.finalized.substitution))
    (raw : RawProperDescendantsPreserved (resultState.toTypedSource (bodyRoots selected))
      (evidenceSource selected) (.expression inferred.id))
    (patterns : resultState.integerPatterns ⊆ selected.body.returned.integerPatterns)
    (literals : resultState.integerLiterals ⊆ selected.body.returned.integerLiterals)
    (requirements : resultState.requirements ⊆ selected.body.returned.requirements)
    (retained : ExpressionRequirementsRetainedAt (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource inferred.id)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource inferred.id)
    (childrenRetained : ExpressionDirectChildrenRetainedAt (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource inferred.id)
    (covered : TemplateScopeCovered selected.body.finalized.typedSource target (.expression inferred.id))
    (actualCovered : ActualContext.Covers selected.body.finalized frames (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  exact constructorApplicationRetained_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursive boundary) True.intro success interfaces extension scope invariant actual
    operational payloadBelow resultBelow expectedBelow payloadSafe resultSafe expectedSafe instantiationValid
    raw patterns literals requirements retained coercionsRetained childrenRetained covered actualCovered

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedFreshConstructor
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

theorem freshConstructorRetained_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ExpressionRetainedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial allocated constructorState resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {id : ExpressionId} {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    {instantiation : DataConstructorInstantiation} {arguments : List Syntax.Expr}
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (dataMember : dataType ∈ inferenceContext.signatures.dataTypes)
    (constructorMember : constructor ∈ dataType.constructors)
    (fresh : Detail.freshDataConstructorInstantiation dataType constructor allocated =
      (instantiation, constructorState))
    (applicationHere : callProvenance (.constructorApplication childFuel inferenceContext expression id instantiation
      arguments expected constructorState inferred resultState))
    (accepted : Detail.inferConstructorApplicationFuel childFuel inferenceContext expression id
      instantiation arguments expected constructorState = .ok (inferred, resultState)) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  have formation := boundary.scope.formation checked
  have catalog := boundary.scope.catalog checked
  have canonical := boundary.scope.canonical checked
  have invariant := boundary.invariant.allocateExpressionId allocation
  have operational := boundary.operational.allocateExpressionId
  rw [allocation] at operational
  have freshInvariant := invariant.freshConstructor dataType constructor
  have freshOperational := operational.freshConstructor dataType constructor
  rw [fresh] at freshInvariant freshOperational
  have properties := Detail.freshDataConstructorInstantiation_inferenceProperties dataType constructor
    allocated invariant.ready
    (formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember allocated.inference.next)
  rw [fresh] at properties
  have binders := invariant.typeParameterBinders
    (by simpa only [boundary.scope.owner, boundary.scope.parameters] using canonical)
  have activeCatalog : SignatureCatalogWellFormed target.signatures := by
    rw [invariant.signatures_eq_whole, ← boundary.scope.signatures]
    exact catalog
  have activeData : dataType ∈ target.signatures.dataTypes := by
    rw [invariant.signatures_eq_whole, ← boundary.scope.signatures]
    exact dataMember
  have range := selected.body.resources.substitutionRangeAdmissible binders
    invariant.signatures_eq_whole invariant.typeParametersEq invariant.declarationEq invariant.residual
  have valid := freshConstructor_admissible_afterSubstitution activeCatalog binders invariant.residual range
    activeData constructorMember fresh
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocation]
    exact boundary.expectedBelow
  have allocatedSame : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have allocatedSafe : ∀ binder ∈ allocated.localBinders, ∀ type ∈ expected,
      ProtectedVariables.Safe binder.scheme.quantified allocated type := by
    rw [allocatedSame]
    exact boundary.expectedSafe
  have freshScope := Detail.freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor allocated
  rw [fresh] at freshScope
  have freshBinders : constructorState.localBinders = allocated.localBinders :=
    congrArg LexicalScope.binders freshScope
  have privacy : ∀ binder ∈ constructorState.localBinders,
      ProtectedVariables.SafeTransport binder.scheme.quantified allocated constructorState ∧
      (∀ type ∈ instantiation.payloadTypes,
        ProtectedVariables.Safe binder.scheme.quantified constructorState type) ∧
      ProtectedVariables.Safe binder.scheme.quantified constructorState instantiation.resultType := by
    intro binder member
    have old : binder ∈ allocated.localBinders := freshBinders ▸ member
    have privateTypes := ProtectedVariables.fresh_constructor (dataType := dataType)
      (constructor := constructor) invariant.ready (operational.quantifiersBelow binder old)
      (formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember 0)
    rw [fresh] at privateTypes
    exact privateTypes
  exact constructorApplicationRetained_for checked descend recursive applicationHere accepted boundary.interfaces boundary.extension
    boundary.scope freshInvariant boundary.actual freshOperational properties.2.2.2.1 properties.2.2.2.2
    (fun type member => (allocatedExpected type member).weaken properties.1.next_le)
    (fun binder member => (privacy binder member).2.1)
    (fun binder member => (privacy binder member).2.2)
    (fun binder member type typeMember =>
      (privacy binder member).1 type (allocatedSafe binder (freshBinders ▸ member) type typeMember))
    valid boundary.rawProper boundary.integerPatterns boundary.integerLiterals boundary.requirements
    boundary.expressionRequirements boundary.coercionPrimaries boundary.directChildren boundary.covered
    boundary.actualCovered

theorem freshConstructorRetained
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial allocated constructorState resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {id : ExpressionId} {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    {instantiation : DataConstructorInstantiation} {arguments : List Syntax.Expr}
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (dataMember : dataType ∈ inferenceContext.signatures.dataTypes)
    (constructorMember : constructor ∈ dataType.constructors)
    (fresh : Detail.freshDataConstructorInstantiation dataType constructor allocated =
      (instantiation, constructorState))
    (accepted : Detail.inferConstructorApplicationFuel childFuel inferenceContext expression id
      instantiation arguments expected constructorState = .ok (inferred, resultState)) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  exact freshConstructorRetained_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursive boundary) boundary allocation dataMember constructorMember fresh True.intro accepted

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedConstructorSoundness
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
  {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
  {selected : BodySelection compiled row fuel}

theorem constructor_call_for {callProvenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ExpressionRetainedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {expression callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    (here : callProvenance (.expression (childFuel + 1) inferenceContext expression expected initial inferred resultState))
    (form : expression.value = .call callee arguments)
    (discovery : Detail.constructorCalleeCandidates inferenceContext initial.allocateExpressionId.2 callee =
      .ok [(dataType, constructor)])
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  generalize allocation : initial.allocateExpressionId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  have found : Detail.constructorCalleeCandidates inferenceContext allocated callee =
      .ok [(dataType, constructor)] := by simpa only [allocation] using discovery
  have members := Detail.constructorCalleeCandidates_success_members found dataType constructor (by simp)
  have success := boundary.accepted
  unfold Detail.inferExprFuel at success
  simp only [allocation, form, found, bind, Except.bind] at success
  generalize fresh : Detail.freshDataConstructorInstantiation dataType constructor allocated = pair at success
  obtain ⟨instantiation, constructorState⟩ := pair
  exact freshConstructorRetained_for checked descend recursive boundary allocation members.1 members.2 fresh
    (descend here (.expression_call_constructor boundary.accepted form allocation found fresh success)) success

theorem constructor_dot_for {callProvenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ExpressionRetainedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr}
    {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
    {arguments : Option (Syntax.DelimitedList Syntax.Expr)} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.expression (childFuel + 1) inferenceContext expression expected initial inferred resultState))
    (form : expression.value = .dotConstructor dot name arguments)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  have formation := boundary.scope.formation checked
  have catalog := boundary.scope.catalog checked
  generalize allocation : initial.allocateExpressionId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  have invariant := boundary.invariant.allocateExpressionId allocation
  have operational := boundary.operational.allocateExpressionId
  rw [allocation] at operational
  have expectedBelow : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocation]
    exact boundary.expectedBelow
  have allocatedSame : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have expectedSafe : ∀ binder ∈ allocated.localBinders, ∀ type ∈ expected,
      ProtectedVariables.Safe binder.scheme.quantified allocated type := by
    rw [allocatedSame]
    exact boundary.expectedSafe
  have success := boundary.accepted
  unfold Detail.inferExprFuel at success
  simp only [allocation, form, bind, Except.bind] at success
  cases found : Detail.contextualConstructorCandidate inferenceContext allocated expected name.value with
  | error error => simp [found] at success
  | ok pair =>
    obtain ⟨dataType, constructor, typeArguments⟩ := pair
    simp only [found] at success
    obtain ⟨dataMember, constructorMember, expectedType, expectedEq, nominalEq⟩ :=
      Detail.contextualConstructorCandidate_success_facts found
    have bounded := Detail.contextualConstructorCandidate_success_instantiation_variablesBelow
      invariant.ready expectedBelow formation found
    have activeCatalog : SignatureCatalogWellFormed target.signatures := by
      rw [invariant.signatures_eq_whole, ← boundary.scope.signatures]
      exact catalog
    have activeData : dataType ∈ target.signatures.dataTypes := by
      rw [invariant.signatures_eq_whole, ← boundary.scope.signatures]
      exact dataMember
    have resultAdmissible : TypeAdmissible target
        (selected.body.finalized.substitution.apply
          (Detail.instantiateDataConstructor dataType constructor typeArguments).resultType) := by
      have expectedTyped := boundary.expectedAdmissible expectedType (by simp [expectedEq])
      have resolved : selected.body.finalized.substitution.apply (allocated.resolve expectedType) =
          selected.body.finalized.substitution.apply expectedType := by
        simpa only [State.resolve, InferState.resolve] using invariant.substitutionExtension expectedType
      rw [← resolved, nominalEq] at expectedTyped
      exact expectedTyped
    have valid := SourceSemantics.DataConstructorInstantiation.Admissible.instantiateDataConstructor_applySubstitution
      activeCatalog activeData constructorMember selected.body.finalized.substitution resultAdmissible
    have privacy : ∀ binder ∈ allocated.localBinders,
        (∀ type ∈ (Detail.instantiateDataConstructor dataType constructor typeArguments).payloadTypes,
          ProtectedVariables.Safe binder.scheme.quantified allocated type) ∧
        ProtectedVariables.Safe binder.scheme.quantified allocated
          (Detail.instantiateDataConstructor dataType constructor typeArguments).resultType := by
      intro binder member
      have accepted : Detail.contextualConstructorCandidate inferenceContext allocated
          (some expectedType) name.value = .ok (dataType, constructor, typeArguments) := expectedEq ▸ found
      exact ProtectedVariables.contextual_constructor invariant.ready formation
        (expectedSafe binder member expectedType (by simp [expectedEq])) accepted
    exact constructorApplicationRetained_for checked descend recursive
      (descend here (.expression_contextual_constructor boundary.accepted form allocation found success)) success boundary.interfaces boundary.extension
      boundary.scope invariant boundary.actual operational bounded.1 bounded.2 expectedBelow
      (fun binder member => (privacy binder member).1)
      (fun binder member => (privacy binder member).2) expectedSafe valid boundary.rawProper
      boundary.integerPatterns boundary.integerLiterals boundary.requirements boundary.expressionRequirements
      boundary.coercionPrimaries boundary.directChildren boundary.covered boundary.actualCovered

theorem constructor_field_for {callProvenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ExpressionRetainedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {expression base : Syntax.Expr}
    {dot : Syntax.SourceSpan} {name : Syntax.Identifier} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.expression (childFuel + 1) inferenceContext expression expected initial inferred resultState))
    (form : expression.value = .field base dot name)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  generalize allocation : initial.allocateExpressionId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  have success := boundary.accepted
  unfold Detail.inferExprFuel at success
  simp only [allocation, form, bind, Except.bind] at success
  cases discovery : Detail.constructorCalleeCandidates inferenceContext allocated expression with
  | error error => simp [discovery] at success
  | ok candidates =>
    cases candidates with
    | nil =>
      simp only [discovery] at success
      repeat' split at success
      all_goals simp_all [throw]
    | cons first rest =>
      obtain ⟨dataType, constructor⟩ := first
      cases rest with
      | cons second tail => simp [discovery] at success
      | nil =>
        simp only [discovery] at success
        have members := Detail.constructorCalleeCandidates_success_members discovery dataType constructor (by simp)
        generalize fresh : Detail.freshDataConstructorInstantiation dataType constructor allocated = pair at success
        obtain ⟨instantiation, constructorState⟩ := pair
        exact freshConstructorRetained_for checked descend recursive boundary allocation members.1 members.2 fresh
          (descend here (.expression_field_constructor boundary.accepted form allocation discovery fresh success)) success

theorem constructor_call
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    (form : expression.value = .call callee arguments)
    (discovery : Detail.constructorCalleeCandidates inferenceContext initial.allocateExpressionId.2 callee =
      .ok [(dataType, constructor)])
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  exact constructor_call_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursive boundary) True.intro form discovery boundary

theorem constructor_dot
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr}
    {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
    {arguments : Option (Syntax.DelimitedList Syntax.Expr)} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : expression.value = .dotConstructor dot name arguments)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  exact constructor_dot_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursive boundary) True.intro form boundary

theorem constructor_field
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression base : Syntax.Expr}
    {dot : Syntax.SourceSpan} {name : Syntax.Identifier} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : expression.value = .field base dot name)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  exact constructor_field_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursive boundary) True.intro form boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedCallSoundness
/-! Actual call dispatch selects constructor, named, builtin or indirect
execution. Every branch consumes the same selected body's child hypotheses. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

theorem expressionRetained_call_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    {inferenceContext : SourceInference.Context} {expression callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.expression (childFuel + 1) inferenceContext expression expected initial inferred resultState))
    (form : expression.value = .call callee arguments)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  generalize allocation : initial.allocateExpressionId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  have invariant := boundary.invariant.allocateExpressionId allocation
  have operational := boundary.operational.allocateExpressionId
  rw [allocation] at operational
  have expectedBelow : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocation]
    exact boundary.expectedBelow
  cases inferExprFuel_success_call_dispatch_provenance_facts form allocation boundary.accepted with
  | constructor discovery fresh application =>
    exact constructor_call_for checked descend (recursive childFuel (Nat.lt_succ_self _)) here form
      (by simpa only [allocation] using discovery) boundary
  | selected nonconstructor argumentsSuccess origin selection recording =>
    have argumentsHere := descend here (.expression_call_arguments boundary.accepted form allocation nonconstructor argumentsSuccess)
    have argumentCalls := OrderedExpressionCalls.of_call descend argumentsHere argumentsSuccess
    exact selectedCall_typing_for checked
      (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self _)))
      boundary invariant operational expectedBelow argumentCalls argumentsSuccess selection recording origin.candidatesSubset
  | builtin nonconstructor argumentsSuccess recording =>
    have argumentsHere := descend here (.expression_call_arguments boundary.accepted form allocation nonconstructor argumentsSuccess)
    exact builtinCall_typing_for checked descend
      (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self _)))
      boundary invariant operational expectedBelow argumentsHere argumentsSuccess recording
  | indirect nonconstructor argumentsSuccess indirect calleeSuccess applicationSuccess recording =>
    have argumentsHere := descend here (.expression_call_arguments boundary.accepted form allocation nonconstructor argumentsSuccess)
    have calleeHere := descend here (.expression_call_callee boundary.accepted form allocation nonconstructor argumentsSuccess indirect calleeSuccess)
    exact indirectCall_typing_for checked descend recursive boundary invariant operational expectedBelow
      argumentsHere argumentsSuccess calleeHere calleeSuccess applicationSuccess recording

theorem expressionRetained_call
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {expression callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : expression.value = .call callee arguments)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  exact expressionRetained_call_for (callProvenance := fun _ => True) checked true_childClosed
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursive smaller less boundary) True.intro form boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedPlaceContracts
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

structure PlaceBoundary (selected : BodySelection compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context)
    (expression : Syntax.Expr) (initial : State) (place : PlaceResolution) (final : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : Detail.inferPlaceFuel childFuel inferenceContext expression initial = .ok (place, final)
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces
    (checkingContext selected).signatures selected.body.finalized.solvedRequirements
    selected.body.finalized.typedSource
  extension : selected.body.finalized.substitution.SemanticallyExtends final.inference.substitution
  scope : CheckingScope selected inferenceContext
  invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant initial (evidenceSource selected)
  rawKeys : ∀ key, .expression key ∈ place.references →
    RawSubtreePreserved (final.toTypedSource (bodyRoots selected)) (evidenceSource selected) (.expression key)
  integerPatterns : final.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : final.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : final.requirements ⊆ selected.body.returned.requirements
  covered : ∀ key, .expression key ∈ place.references →
    TemplateScopeCovered selected.body.finalized.typedSource target (.expression key)
  actualCovered : ∀ key, .expression key ∈ place.references →
    ActualContext.Covers selected.body.finalized frames (.expression key)

def PlaceConclusion (selected : BodySelection compiled row fuel)
    (place : PlaceResolution) (final : State) (target : SourceSemantics.Context) : Prop :=
  SourcePlaceHasType selected.body.finalized.typedSource target
    (place.applySubstitution selected.body.finalized.substitution)
    (selected.body.finalized.substitution.apply place.type) ∧
  GeneralizedActualStateInvariant final (evidenceSource selected) ∧
  ∀ binder ∈ final.localBinders,
    ProtectedVariables.Safe binder.scheme.quantified final place.type

def PlaceRootedSoundness (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {expression : Syntax.Expr}
    {initial final : State} {place : PlaceResolution}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    PlaceBoundary selected childFuel inferenceContext expression initial place final frames target →
    PlaceConclusion selected place final target

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledProvenanceStatementContracts
/-! Exact-call provenance accompanies the existing semantic boundaries.
Generalization barriers are requested only for those same calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

def StatementRootedSoundnessFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.statement childFuel inferenceContext statement expectedReturn initial result) →
    (∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn) →
    TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
    StatementBoundary selected childFuel inferenceContext statement expectedReturn
      initial result frames target →
    StatementConclusion selected inferenceContext expectedReturn result frames target

def StatementsRootedSoundnessFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.BlockResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.statements childFuel inferenceContext statements expectedReturn initial result) →
    (∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn) →
    TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
    StatementsBoundary selected childFuel inferenceContext statements expectedReturn
      initial result frames target →
    StatementsConclusion selected inferenceContext expectedReturn result frames target

def ForItemRootedSoundnessFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {item : Syntax.ForItem} {expectedReturn : Ty}
    {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.forItem childFuel inferenceContext item initial inferred final) →
    ForItemBoundary selected childFuel inferenceContext item expectedReturn
      initial inferred final frames target →
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target

def ForItemsRootedSoundnessFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {items : List Syntax.ForItem} {expectedReturn : Ty}
    {initial : State} {result : Detail.InferredForItems}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.forItems childFuel inferenceContext items initial result) →
    ForItemsBoundary selected childFuel inferenceContext items expectedReturn
      initial result frames target →
    ForItemsConclusion selected inferenceContext expectedReturn result frames target

def PlaceRootedSoundnessFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {expression : Syntax.Expr}
    {initial final : State} {place : PlaceResolution}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.place childFuel inferenceContext expression initial place final) →
    PlaceBoundary selected childFuel inferenceContext expression initial place final frames target →
    PlaceConclusion selected place final target

structure BodyInitializerBarriersFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) : Prop where
  statement : ∀ {source : Syntax.Statement} {expectedReturn : Ty}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
      (occurrence : BodyInitializerOccurrence selected source),
    provenance (.statement (occurrence.childFuel + 1) occurrence.inferenceContext
      source expectedReturn occurrence.entry occurrence.result) →
    StatementBoundary selected (occurrence.childFuel + 1) occurrence.inferenceContext source expectedReturn
      occurrence.entry occurrence.result frames target →
    GeneralizationBarrierTransport occurrence.receipt.ready occurrence.receipt.locals
      occurrence.entry.nextRequirement (occurrence.receipt.ready.resolve occurrence.receipt.value.type)
      selected.body.finalized.substitution target (localSchemeTemplateIds occurrence.initializerBinding.binder)
  header : ∀ {childFuel : Nat} {inferenceContext : SourceInference.Context} {item : Syntax.ForItem}
      {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.forItem (childFuel + 1) inferenceContext item initial inferred final) →
    ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target →
    ∀ receipt : LocalHeaderRequirementTiming.Receipt childFuel inferenceContext item initial (inferred, final),
    GeneralizationBarrierTransport receipt.ready receipt.locals initial.nextRequirement
      (receipt.ready.resolve receipt.value.type) selected.body.finalized.substitution target
      (localSchemeTemplateIds (receipt.binding.1.applySubstitution selected.body.finalized.substitution))

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedConditionalSoundness
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

private theorem safe_after_expression
    {childFuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {expected laterExpected : Option Ty} {initial final : State} {value : InferredExpression}
    {source : TypedSource}
    (operational : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (expectedSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ expected,
      ProtectedVariables.Safe binder.scheme.quantified initial type)
    (laterSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ laterExpected,
      ProtectedVariables.Safe binder.scheme.quantified initial type)
    (accepted : Detail.inferExprFuel childFuel context expression expected initial = .ok (value, final)) :
    ∀ binder ∈ final.localBinders, ∀ type ∈ laterExpected,
      ProtectedVariables.Safe binder.scheme.quantified final type := by
  intro binder member type typeMember
  have binders := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq accepted)
  change final.localBinders = initial.localBinders at binders
  have entering : binder ∈ initial.localBinders := binders ▸ member
  exact (ProtectedVariables.inferExprFuel_private binder.scheme.quantified childFuel context expression
    expected initial ready operational.requirements (operational.quantifiersBelow binder entering)
    (operational.privacy binder entering) catalog formation canonical expectedBelow
    (expectedSafe binder entering) _ accepted).1 type (laterSafe binder entering type typeMember)

/-- Conditional inference threads privacy through the condition and both branches before assembling their common final-source typing. -/
theorem expressionRetained_conditional_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ExpressionRetainedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {expression condition thenBranch elseBranch : Syntax.Expr}
    {question colon : Syntax.SourceSpan}
    {expected : Option Ty} {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.expression (childFuel + 1) inferenceContext expression expected initial inferred resultState))
    (expressionEq : expression.value = .conditional condition question thenBranch colon elseBranch)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  have resources := selected.body.resources
  have signatureFormation := boundary.scope.formation checked
  have functionsCanonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  have canonical := boundary.scope.canonical checked
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have allocatedInvariant := boundary.invariant.allocateExpressionId allocationEq
  have allocatedOperational : GeneralizedActualStateInvariant allocated (evidenceSource selected) := by
    rw [← show initial.allocateExpressionId.2 = allocated from congrArg Prod.snd allocationEq]
    exact boundary.operational.allocateExpressionId
  have allocatedSafe : ∀ binder ∈ allocated.localBinders, ∀ type ∈ expected,
      ProtectedVariables.Safe binder.scheme.quantified allocated type := by
    rw [← show initial.allocateExpressionId.2 = allocated from congrArg Prod.snd allocationEq]
    exact boundary.expectedSafe
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]
    exact boundary.expectedBelow
  obtain ⟨conditionResult, conditionState, thenResult, thenState, elseResult,
      elseState, unifiedState, conditionSuccess, thenSuccess, elseSuccess,
      unifySuccess, recorded⟩ :=
    Detail.inferExprFuel_success_conditional_facts expressionEq allocationEq
      boundary.accepted
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expectedType member
      simp only [Option.mem_def] at member
      have expectedTypeEq : expectedType = .bool :=
        (Option.some.inj member).symm
      rw [expectedTypeEq]
      change TypeSystem.Ty.VariablesBelow allocated.inference.next
        (.constructor (.builtin .bool))
      exact TypeSystem.Ty.variablesBelow_constructor _ _) conditionSuccess
  have expectedAtCondition : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow conditionState.inference.next := by
    intro expectedType member
    exact (allocatedExpected expectedType member).weaken
      conditionProperties.1.next_le
  have thenProperties := Detail.inferExprFuel_inferenceProperties
    conditionProperties.2.1 signatureFormation functionsCanonical
      expectedAtCondition thenSuccess
  have expectedAtThen : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow thenState.inference.next := by
    intro expectedType member
    exact (expectedAtCondition expectedType member).weaken
      thenProperties.1.next_le
  have elseProperties := Detail.inferExprFuel_inferenceProperties
    thenProperties.2.1 signatureFormation functionsCanonical expectedAtThen
      elseSuccess
  have thenAtElse : thenResult.type.VariablesBelow
      elseState.inference.next :=
    thenProperties.2.2.weaken elseProperties.1.next_le
  have unifyProgress := Detail.unify_inferenceProgress
    elseProperties.2.1.solved thenAtElse elseProperties.2.2 unifySuccess
  have unifiedReady := Detail.unify_preserves_inferenceReady
    elseProperties.2.1 thenAtElse elseProperties.2.2 unifySuccess
  have allocatedToUnified : allocated.InferenceProgress unifiedState :=
    conditionProperties.1.trans
      (thenProperties.1.trans (elseProperties.1.trans unifyProgress))
  have expectedAtUnified : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow unifiedState.inference.next := by
    intro expectedType member
    exact (allocatedExpected expectedType member).weaken
      allocatedToUnified.next_le
  have thenAtUnified : thenResult.type.VariablesBelow
      unifiedState.inference.next :=
    thenAtElse.weaken unifyProgress.next_le
  have resolvedThenBelow :
      (unifiedState.resolve thenResult.type).VariablesBelow
        unifiedState.inference.next :=
    unifiedReady.solved.variablesBelow_apply thenAtUnified
  have recordedProperties :=
    Detail.recordExpressionWithExpected_inferenceProperties unifiedReady
      resolvedThenBelow expectedAtUnified recorded
  have laterUnified : selected.body.finalized.substitution.SemanticallyExtends
      unifiedState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans boundary.extension
      recordedProperties.1.substitution_extends
  have laterElse : selected.body.finalized.substitution.SemanticallyExtends
      elseState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterUnified
      unifyProgress.substitution_extends
  have laterThen : selected.body.finalized.substitution.SemanticallyExtends
      thenState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterElse
      elseProperties.1.substitution_extends
  have laterCondition : selected.body.finalized.substitution.SemanticallyExtends
      conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterThen
      thenProperties.1.substitution_extends
  have allocatedBelow := allocatedInvariant.nodesBelow
  have conditionBelow : conditionState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends conditionSuccess
      ).nodesBelowNextOccurrence allocatedBelow
  have thenBelow : thenState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends thenSuccess
      ).nodesBelowNextOccurrence conditionBelow
  have elseBelow : elseState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends elseSuccess
      ).nodesBelowNextOccurrence thenBelow
  have unifiedBelow : unifiedState.NodesBelowNextOccurrence :=
    (Detail.unify_occurrenceBoundExtends unifySuccess
      ).nodesBelowNextOccurrence elseBelow
  have conditionToThen :=
    inferExprFuel_success_typingSourceExtends thenSuccess conditionBelow (bodyRoots selected)
  have thenToElse :=
    inferExprFuel_success_typingSourceExtends elseSuccess thenBelow (bodyRoots selected)
  have elseToUnified : TypingSourceExtends
      (elseState.toTypedSource (bodyRoots selected)) (unifiedState.toTypedSource (bodyRoots selected)) := by
    constructor
    · change unifiedState.owner = elseState.owner
      have headerEq := Detail.unify_state_header unifySuccess
      simpa [Frontend.SourceInference.State.header] using
        congrArg Frontend.SourceInference.State.Header.owner headerEq
    · change elseState.nodes <+: unifiedState.nodes
      rw [(Detail.unify_occurrenceState_eq unifySuccess).1]
      exact List.prefix_rfl
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have conditionOwner : conditionState.owner = allocated.owner :=
    Detail.inferExprFuel_preserves_owner conditionSuccess
  have thenOwner : thenState.owner = conditionState.owner :=
    Detail.inferExprFuel_preserves_owner thenSuccess
  have elseOwner : elseState.owner = thenState.owner :=
    Detail.inferExprFuel_preserves_owner elseSuccess
  have unifiedOwner : unifiedState.owner = elseState.owner := by
    have headerEq := Detail.unify_state_header unifySuccess
    simpa [Frontend.SourceInference.State.header] using
      congrArg Frontend.SourceInference.State.Header.owner headerEq
  have parentOwner : resultState.owner = initial.owner :=
    Detail.inferExprFuel_preserves_owner boundary.accepted
  have unifiedToParent : TypingSourceExtends
      (unifiedState.toTypedSource (bodyRoots selected)) (resultState.toTypedSource (bodyRoots selected)) := by
    constructor
    · exact parentOwner.trans
        (allocatedOwner.symm.trans
          (conditionOwner.symm.trans
            (thenOwner.symm.trans
              (elseOwner.symm.trans unifiedOwner.symm))))
    · exact recordExpressionWithExpected_success_nodesPrefix recorded
  have conditionToParent :=
    TypingSourceExtends.trans conditionToThen
      (TypingSourceExtends.trans thenToElse
        (TypingSourceExtends.trans elseToUnified unifiedToParent))
  have thenToParent :=
    TypingSourceExtends.trans thenToElse
      (TypingSourceExtends.trans elseToUnified unifiedToParent)
  have elseToParent :=
    TypingSourceExtends.trans elseToUnified unifiedToParent
  have unifiedIntegerLiteralsSubset :
      unifiedState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    rw [Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact member
  have elseIntegerLiteralsSubset :
      elseState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    apply unifiedIntegerLiteralsSubset
    rw [Detail.unify_integerLiterals unifySuccess]
    exact member
  have thenIntegerLiteralsSubset :
      thenState.integerLiterals ⊆ resultState.integerLiterals :=
    List.Subset.trans
      (Detail.inferExprFuel_integerLiterals_subset elseSuccess)
      elseIntegerLiteralsSubset
  have conditionIntegerLiteralsSubset :
      conditionState.integerLiterals ⊆ resultState.integerLiterals :=
    List.Subset.trans
      (Detail.inferExprFuel_integerLiterals_subset thenSuccess)
      thenIntegerLiteralsSubset
  have unifiedIntegerPatternsSubset :
      unifiedState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    rw [recordExpressionWithExpected_integerPatterns_eq recorded]
    exact member
  have elseIntegerPatternsSubset :
      elseState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    apply unifiedIntegerPatternsSubset
    rw [(Detail.unify_integerPatternMetadata_eq unifySuccess).1]
    exact member
  have thenIntegerPatternsSubset :
      thenState.integerPatterns ⊆ resultState.integerPatterns :=
    List.Subset.trans
      (Detail.inferExprFuel_integerPatterns_subset elseSuccess)
      elseIntegerPatternsSubset
  have conditionIntegerPatternsSubset :
      conditionState.integerPatterns ⊆ resultState.integerPatterns :=
    List.Subset.trans
      (Detail.inferExprFuel_integerPatterns_subset thenSuccess)
      thenIntegerPatternsSubset
  have unifiedRequirementsSubset :
      unifiedState.requirements ⊆ resultState.requirements :=
    Detail.recordExpressionWithExpected_requirements_subset recorded
  have elseRequirementsSubset :
      elseState.requirements ⊆ resultState.requirements := by
    intro requirement member
    apply unifiedRequirementsSubset
    rw [Detail.unify_requirements_eq unifySuccess]
    exact member
  have thenRequirementsSubset :
      thenState.requirements ⊆ resultState.requirements :=
    List.Subset.trans
      (Detail.inferExprFuel_requirements_subset elseSuccess)
      elseRequirementsSubset
  have conditionRequirementsSubset :
      conditionState.requirements ⊆ resultState.requirements :=
    List.Subset.trans
      (Detail.inferExprFuel_requirements_subset thenSuccess)
      thenRequirementsSubset
  have conditionExpected : ∀ type ∈ (some Ty.bool : Option Ty), type.VariablesBelow allocated.inference.next := by
    intro type member
    have same : type = Ty.bool := (Option.some.inj member).symm
    subst type
    exact Ty.variablesBelow_constructor _ _
  have conditionInvariant := allocatedInvariant.ofExpression signatureFormation functionsCanonical
    conditionExpected laterCondition conditionSuccess
  have thenInvariant := conditionInvariant.ofExpression signatureFormation functionsCanonical
    expectedAtCondition laterThen thenSuccess
  have conditionSafe : ∀ binder ∈ allocated.localBinders, ∀ type ∈ (some Ty.bool : Option Ty),
      ProtectedVariables.Safe binder.scheme.quantified allocated type := by
    intro binder _ type member
    have same : type = Ty.bool := (Option.some.inj member).symm
    subst type
    exact ProtectedVariables.safe_closed _ _ (Ty.variablesBelow_constructor _ _)
  have expectedSafeAtCondition := safe_after_expression allocatedOperational allocatedInvariant.ready
    catalog signatureFormation functionsCanonical conditionExpected conditionSafe allocatedSafe conditionSuccess
  have conditionOperational := allocatedOperational.ofExpression allocatedInvariant.ready catalog
    signatureFormation functionsCanonical conditionExpected conditionSafe conditionSuccess
  have expectedSafeAtThen := safe_after_expression conditionOperational conditionInvariant.ready
    catalog signatureFormation functionsCanonical expectedAtCondition expectedSafeAtCondition
    expectedSafeAtCondition thenSuccess
  have thenOperational := conditionOperational.ofExpression conditionInvariant.ready catalog
    signatureFormation functionsCanonical expectedAtCondition expectedSafeAtCondition thenSuccess
  obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded (bodyRoots selected)
  have edge : ∀ child ∈ [conditionResult.id, thenResult.id, elseResult.id],
      DirectChild (resultState.toTypedSource (bodyRoots selected)) (.expression inferred.id) (.expression child) := by
    intro child member
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simpa [nodeChildIds, Node.references, ExpressionForm.references] using
      (List.mem_map.mpr ⟨child, member, rfl⟩ : NodeId.expression child ∈
        [conditionResult.id, thenResult.id, elseResult.id].map NodeId.expression)
  have conditionEdge := edge conditionResult.id (by simp)
  have conditionTypeRaw := expressionRooted_of_retained_for checked recursive
    (descend here (.expression_conditional_condition boundary.accepted expressionEq allocationEq conditionSuccess)) ({
    accepted := conditionSuccess
    interfaces := boundary.interfaces
    extension := laterCondition
    scope := boundary.scope
    invariant := allocatedInvariant
    actual := boundary.actual
    operational := allocatedOperational
    expectedBelow := conditionExpected
    expectedAdmissible := by
      intro type member
      have same : type = .bool := (Option.some.inj member).symm
      subst type
      exact TypeAdmissible.bool (boundary.invariant.typeParameterBinders (by
        simpa [boundary.scope.owner, boundary.scope.parameters] using canonical))
    expectedSafe := conditionSafe
    integerPatterns := List.Subset.trans conditionIntegerPatternsSubset boundary.integerPatterns
    integerLiterals := List.Subset.trans conditionIntegerLiteralsSubset boundary.integerLiterals
    requirements := List.Subset.trans conditionRequirementsSubset boundary.requirements
    covered := boundary.covered.expressionChild resources.graph_closed (boundary.directChildren conditionEdge)
    actualCovered := boundary.actualCovered.directChild (boundary.directChildren conditionEdge)
    rawSubtree := (boundary.rawProper.childSubtree conditionEdge).monoBefore conditionToParent } :
    RootedExpressionBoundary selected childFuel inferenceContext condition (some .bool)
      allocated conditionResult conditionState frames target)
  have thenEdge := edge thenResult.id (by simp)
  have thenTypeRaw := expressionRooted_of_retained_for checked recursive
    (descend here (.expression_conditional_then boundary.accepted expressionEq allocationEq conditionSuccess thenSuccess)) ({
    accepted := thenSuccess
    interfaces := boundary.interfaces
    extension := laterThen
    scope := boundary.scope
    invariant := conditionInvariant
    actual := boundary.actual
    operational := conditionOperational
    expectedBelow := expectedAtCondition
    expectedAdmissible := boundary.expectedAdmissible
    expectedSafe := expectedSafeAtCondition
    integerPatterns := List.Subset.trans thenIntegerPatternsSubset boundary.integerPatterns
    integerLiterals := List.Subset.trans thenIntegerLiteralsSubset boundary.integerLiterals
    requirements := List.Subset.trans thenRequirementsSubset boundary.requirements
    covered := boundary.covered.expressionChild resources.graph_closed (boundary.directChildren thenEdge)
    actualCovered := boundary.actualCovered.directChild (boundary.directChildren thenEdge)
    rawSubtree := (boundary.rawProper.childSubtree thenEdge).monoBefore thenToParent } :
    RootedExpressionBoundary selected childFuel inferenceContext thenBranch expected
      conditionState thenResult thenState frames target)
  have elseEdge := edge elseResult.id (by simp)
  have elseTypeRaw := expressionRooted_of_retained_for checked recursive
    (descend here (.expression_conditional_else boundary.accepted expressionEq allocationEq conditionSuccess thenSuccess elseSuccess)) ({
    accepted := elseSuccess
    interfaces := boundary.interfaces
    extension := laterElse
    scope := boundary.scope
    invariant := thenInvariant
    actual := boundary.actual
    operational := thenOperational
    expectedBelow := expectedAtThen
    expectedAdmissible := boundary.expectedAdmissible
    expectedSafe := expectedSafeAtThen
    integerPatterns := List.Subset.trans elseIntegerPatternsSubset boundary.integerPatterns
    integerLiterals := List.Subset.trans elseIntegerLiteralsSubset boundary.integerLiterals
    requirements := List.Subset.trans elseRequirementsSubset boundary.requirements
    covered := boundary.covered.expressionChild resources.graph_closed (boundary.directChildren elseEdge)
    actualCovered := boundary.actualCovered.directChild (boundary.directChildren elseEdge)
    rawSubtree := (boundary.rawProper.childSubtree elseEdge).monoBefore elseToParent } :
    RootedExpressionBoundary selected childFuel inferenceContext elseBranch expected
      thenState elseResult elseState frames target)
  have conditionEq : selected.body.finalized.substitution.apply conditionResult.type =
      .bool := by
    simpa using Detail.inferExprFuel_expected_type_apply_eq conditionSuccess
      laterCondition
  have conditionType : ExpressionHasType selected.body.finalized.typedSource target
      conditionResult.id .bool := by
    rw [← conditionEq]
    exact conditionTypeRaw
  have resolvedThenEq :
      selected.body.finalized.substitution.apply
          (unifiedState.resolve thenResult.type) =
        selected.body.finalized.substitution.apply thenResult.type := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterUnified thenResult.type
  have resolvedElseEq :
      selected.body.finalized.substitution.apply
          (unifiedState.resolve elseResult.type) =
        selected.body.finalized.substitution.apply elseResult.type := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterUnified elseResult.type
  have unifiedEq : unifiedState.resolve thenResult.type =
      unifiedState.resolve elseResult.type := by
    simpa [Frontend.SourceInference.State.resolve] using
      Detail.unify_resolve_eq unifySuccess
  have branchEq : selected.body.finalized.substitution.apply thenResult.type =
      selected.body.finalized.substitution.apply elseResult.type := by
    calc
      selected.body.finalized.substitution.apply thenResult.type =
          selected.body.finalized.substitution.apply
            (unifiedState.resolve thenResult.type) := resolvedThenEq.symm
      _ = selected.body.finalized.substitution.apply
          (unifiedState.resolve elseResult.type) :=
        congrArg selected.body.finalized.substitution.apply unifiedEq
      _ = selected.body.finalized.substitution.apply elseResult.type := resolvedElseEq
  have thenType : ExpressionHasType selected.body.finalized.typedSource target thenResult.id
      (selected.body.finalized.substitution.apply
        (unifiedState.resolve thenResult.type)) := by
    rw [resolvedThenEq]
    exact thenTypeRaw
  have elseType : ExpressionHasType selected.body.finalized.typedSource target elseResult.id
      (selected.body.finalized.substitution.apply
        (unifiedState.resolve thenResult.type)) := by
    rw [resolvedThenEq, branchEq]
    exact elseTypeRaw
  have formType : ExpressionFormHasRawType selected.body.finalized.typedSource target
      ((ExpressionForm.conditional conditionResult.id thenResult.id
        elseResult.id).applySubstitution selected.body.finalized.substitution)
      (selected.body.finalized.substitution.apply
        (unifiedState.resolve thenResult.type)) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution] using
      ExpressionFormHasRawType.conditional conditionType thenType elseType
  exact recordExpressionWithExpected_success_expressionTypingBase_actual resources boundary.interfaces
    recorded boundary.extension boundary.requirements boundary.expressionRequirements boundary.coercionPrimaries
    catalog boundary.scope.signatures boundary.invariant formType thenType.type_admissible boundary.covered

theorem expressionRetained_conditional
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression condition thenBranch elseBranch : Syntax.Expr}
    {question colon : Syntax.SourceSpan}
    {expected : Option Ty} {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (expressionEq : expression.value = .conditional condition question thenBranch colon elseBranch)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  exact expressionRetained_conditional_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursive boundary) True.intro expressionEq boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedIndexSoundness
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend Frontend.SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

private theorem fresh_eq_typingSourceExtends
    {initial final : Frontend.SourceInference.State}
    {type : TypeSystem.Ty}
    (success : initial.fresh = (type, final))
    (roots : List NodeId := []) :
    TypingSourceExtends (initial.toTypedSource roots)
      (final.toTypedSource roots) := by
  have finalEq : initial.fresh.2 = final := congrArg Prod.snd success
  rw [← finalEq]
  exact .refl _

private theorem fresh_eq_integerLiterals_eq
    {initial final : Frontend.SourceInference.State}
    {type : TypeSystem.Ty}
    (success : initial.fresh = (type, final)) :
    final.integerLiterals = initial.integerLiterals := by
  have finalEq : initial.fresh.2 = final := congrArg Prod.snd success
  rw [← finalEq]
  rfl

private theorem fresh_eq_integerPatterns_eq
    {initial final : Frontend.SourceInference.State}
    {type : TypeSystem.Ty}
    (success : initial.fresh = (type, final)) :
    final.integerPatterns = initial.integerPatterns := by
  have finalEq : initial.fresh.2 = final := congrArg Prod.snd success
  rw [← finalEq]
  rfl

private theorem fresh_eq_requirements_eq
    {initial final : Frontend.SourceInference.State}
    {type : TypeSystem.Ty}
    (success : initial.fresh = (type, final)) :
    final.requirements = initial.requirements := by
  have finalEq : initial.fresh.2 = final := congrArg Prod.snd success
  rw [← finalEq]
  rfl

private theorem unify_success_typingSourceExtends
    {initial final : Frontend.SourceInference.State}
    {left right : TypeSystem.Ty}
    (success : Detail.unify initial left right = .ok final)
    (roots : List NodeId := []) :
    TypingSourceExtends (initial.toTypedSource roots)
      (final.toTypedSource roots) := by
  constructor
  · change final.owner = initial.owner
    have headerEq := Detail.unify_state_header success
    simpa [Frontend.SourceInference.State.header] using
      congrArg Frontend.SourceInference.State.Header.owner headerEq
  · change initial.nodes <+: final.nodes
    rw [(Detail.unify_occurrenceState_eq success).1]
    exact List.prefix_rfl

theorem expressionRetained_index_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed provenance)
    (recursive : ExpressionRetainedSoundnessFor provenance selected childFuel)
    {inferenceContext : SourceInference.Context} {expression baseExpression indexExpression : Syntax.Expr}
    {brackets : Syntax.SourceSpan} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : provenance (.expression (childFuel + 1) inferenceContext expression expected
      initial inferred resultState))
    (expressionEq : expression.value = .index baseExpression brackets indexExpression)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target) :
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
  have rawProper := boundary.rawProper
  have actualCovered := boundary.actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational : GeneralizedActualStateInvariant allocated (evidenceSource selected) := by
    rw [← show initial.allocateExpressionId.2 = allocated from congrArg Prod.snd allocationEq]
    exact boundary.operational.allocateExpressionId
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]
    exact expectedBelow
  obtain ⟨baseResult, baseState, keyType, keyState, valueType, valueState,
      mappingState, indexResult, indexState, baseSuccess, keyFresh, valueFresh,
      mappingSuccess, indexSuccess, recorded⟩ :=
    Detail.inferExprFuel_success_index_facts expressionEq allocationEq success
  have baseProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expectedType member
      simp at member) baseSuccess
  have keyProperties := Detail.fresh_eq_inferenceProperties
    baseProperties.2.1 keyFresh
  have valueProperties := Detail.fresh_eq_inferenceProperties
    keyProperties.2.1 valueFresh
  have baseAtValue : baseResult.type.VariablesBelow
      valueState.inference.next :=
    baseProperties.2.2.weaken
      (keyProperties.1.trans valueProperties.1).next_le
  have keyAtValue : keyType.VariablesBelow valueState.inference.next :=
    keyProperties.2.2.weaken valueProperties.1.next_le
  have mappingBelow : (TypeSystem.Ty.mapping keyType valueType).VariablesBelow
      valueState.inference.next :=
    (TypeSystem.Ty.variablesBelow_mapping_iff _ _ _).2
      ⟨keyAtValue, valueProperties.2.2⟩
  have unifyProgress := Detail.unify_inferenceProgress
    valueProperties.2.1.solved baseAtValue mappingBelow mappingSuccess
  have mappingReady := Detail.unify_preserves_inferenceReady
    valueProperties.2.1 baseAtValue mappingBelow mappingSuccess
  have keyAtMapping : keyType.VariablesBelow mappingState.inference.next :=
    keyAtValue.weaken unifyProgress.next_le
  have resolvedKeyBelow :
      (mappingState.resolve keyType).VariablesBelow
        mappingState.inference.next :=
    mappingReady.solved.variablesBelow_apply keyAtMapping
  have indexProperties := Detail.inferExprFuel_inferenceProperties
    mappingReady signatureFormation functionsCanonical (by
      intro expectedType member
      simp only [Option.mem_def] at member
      have expectedTypeEq : expectedType = mappingState.resolve keyType :=
        (Option.some.inj member).symm
      rw [expectedTypeEq]
      exact resolvedKeyBelow) indexSuccess
  have allocatedToIndex : allocated.InferenceProgress indexState :=
    baseProperties.1.trans
      (keyProperties.1.trans
        (valueProperties.1.trans
          (unifyProgress.trans indexProperties.1)))
  have expectedAtIndex : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow indexState.inference.next := by
    intro expectedType member
    exact (allocatedExpected expectedType member).weaken allocatedToIndex.next_le
  have valueAtIndex : valueType.VariablesBelow indexState.inference.next :=
    valueProperties.2.2.weaken
      (unifyProgress.trans indexProperties.1).next_le
  have resolvedValueBelow :
      (indexState.resolve valueType).VariablesBelow
        indexState.inference.next :=
    indexProperties.2.1.solved.variablesBelow_apply valueAtIndex
  have recordedProperties :=
    Detail.recordExpressionWithExpected_inferenceProperties
      indexProperties.2.1 resolvedValueBelow expectedAtIndex recorded
  have laterIndex : finalized.substitution.SemanticallyExtends
      indexState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans resultSubstitutionExtension
      recordedProperties.1.substitution_extends
  have laterMapping : finalized.substitution.SemanticallyExtends
      mappingState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterIndex
      indexProperties.1.substitution_extends
  have allocatedBelow := allocatedInvariant.nodesBelow
  have baseBelow : baseState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends baseSuccess
      ).nodesBelowNextOccurrence allocatedBelow
  have keyBelow : keyState.NodesBelowNextOccurrence := by
    have below :=
      Frontend.SourceInference.State.fresh_preserves_nodesBelowNextOccurrence
        baseState baseBelow
    have stateEq : baseState.fresh.2 = keyState := congrArg Prod.snd keyFresh
    simpa [stateEq] using below
  have valueBelow : valueState.NodesBelowNextOccurrence := by
    have below :=
      Frontend.SourceInference.State.fresh_preserves_nodesBelowNextOccurrence
        keyState keyBelow
    have stateEq : keyState.fresh.2 = valueState :=
      congrArg Prod.snd valueFresh
    simpa [stateEq] using below
  have mappingNodesBelow : mappingState.NodesBelowNextOccurrence :=
    (Detail.unify_occurrenceBoundExtends mappingSuccess
      ).nodesBelowNextOccurrence valueBelow
  have indexBelow : indexState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends indexSuccess
      ).nodesBelowNextOccurrence mappingNodesBelow
  have baseToKey := fresh_eq_typingSourceExtends keyFresh roots
  have keyToValue := fresh_eq_typingSourceExtends valueFresh roots
  have valueToMapping := unify_success_typingSourceExtends mappingSuccess roots
  have mappingToIndex :=
    inferExprFuel_success_typingSourceExtends indexSuccess mappingNodesBelow roots
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have baseOwner : baseState.owner = allocated.owner :=
    Detail.inferExprFuel_preserves_owner baseSuccess
  have parentOwner : resultState.owner = initial.owner :=
    Detail.inferExprFuel_preserves_owner success
  have indexToParent : TypingSourceExtends
      (indexState.toTypedSource roots) (resultState.toTypedSource roots) := by
    constructor
    · exact parentOwner.trans
        (allocatedOwner.symm.trans
          (baseOwner.symm.trans
            (baseToKey.owner_eq.symm.trans
              (keyToValue.owner_eq.symm.trans
                (valueToMapping.owner_eq.symm.trans
                  mappingToIndex.owner_eq.symm)))))
    · exact recordExpressionWithExpected_success_nodesPrefix recorded
  have baseToParent :=
    TypingSourceExtends.trans baseToKey
      (TypingSourceExtends.trans keyToValue
        (TypingSourceExtends.trans valueToMapping
          (TypingSourceExtends.trans mappingToIndex indexToParent)))
  have indexIntegerLiteralsSubset :
      indexState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    rw [Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact member
  have mappingIntegerLiteralsSubset :
      mappingState.integerLiterals ⊆ resultState.integerLiterals :=
    List.Subset.trans
      (Detail.inferExprFuel_integerLiterals_subset indexSuccess)
      indexIntegerLiteralsSubset
  have valueIntegerLiteralsSubset :
      valueState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    apply mappingIntegerLiteralsSubset
    rw [Detail.unify_integerLiterals mappingSuccess]
    exact member
  have keyIntegerLiteralsSubset :
      keyState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    apply valueIntegerLiteralsSubset
    rw [fresh_eq_integerLiterals_eq valueFresh]
    exact member
  have baseIntegerLiteralsSubset :
      baseState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    apply keyIntegerLiteralsSubset
    rw [fresh_eq_integerLiterals_eq keyFresh]
    exact member
  have indexIntegerPatternsSubset :
      indexState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    rw [recordExpressionWithExpected_integerPatterns_eq recorded]
    exact member
  have mappingIntegerPatternsSubset :
      mappingState.integerPatterns ⊆ resultState.integerPatterns :=
    List.Subset.trans
      (Detail.inferExprFuel_integerPatterns_subset indexSuccess)
      indexIntegerPatternsSubset
  have valueIntegerPatternsSubset :
      valueState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    apply mappingIntegerPatternsSubset
    rw [(Detail.unify_integerPatternMetadata_eq mappingSuccess).1]
    exact member
  have keyIntegerPatternsSubset :
      keyState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    apply valueIntegerPatternsSubset
    rw [fresh_eq_integerPatterns_eq valueFresh]
    exact member
  have baseIntegerPatternsSubset :
      baseState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    apply keyIntegerPatternsSubset
    rw [fresh_eq_integerPatterns_eq keyFresh]
    exact member
  have indexRequirementsSubset :
      indexState.requirements ⊆ resultState.requirements :=
    Detail.recordExpressionWithExpected_requirements_subset recorded
  have mappingRequirementsSubset :
      mappingState.requirements ⊆ resultState.requirements :=
    List.Subset.trans
      (Detail.inferExprFuel_requirements_subset indexSuccess)
      indexRequirementsSubset
  have valueRequirementsSubset :
      valueState.requirements ⊆ resultState.requirements := by
    intro requirement member
    apply mappingRequirementsSubset
    rw [Detail.unify_requirements_eq mappingSuccess]
    exact member
  have keyRequirementsSubset :
      keyState.requirements ⊆ resultState.requirements := by
    intro requirement member
    apply valueRequirementsSubset
    rw [fresh_eq_requirements_eq valueFresh]
    exact member
  have baseRequirementsSubset :
      baseState.requirements ⊆ resultState.requirements := by
    intro requirement member
    apply keyRequirementsSubset
    rw [fresh_eq_requirements_eq keyFresh]
    exact member
  have laterValue := laterMapping.trans unifyProgress.substitution_extends
  have laterKey := laterValue.trans valueProperties.1.substitution_extends
  have laterBase := laterKey.trans keyProperties.1.substitution_extends
  have baseInvariant := allocatedInvariant.ofExpression signatureFormation functionsCanonical
    (by simp) laterBase baseSuccess
  have keyEq : baseState.fresh.2 = keyState := congrArg Prod.snd keyFresh
  have valueEq : keyState.fresh.2 = valueState := congrArg Prod.snd valueFresh
  have keyInvariant : RecursiveExpressionInvariant wholeContext finalized keyState semanticContext := by
    simpa only [keyEq] using baseInvariant.fresh (by simpa only [keyEq] using laterKey)
  have valueInvariant : RecursiveExpressionInvariant wholeContext finalized valueState semanticContext := by
    simpa only [valueEq] using keyInvariant.fresh (by simpa only [valueEq] using laterValue)
  have mappingInvariant := valueInvariant.unify baseAtValue mappingBelow laterMapping mappingSuccess
  have baseOperational := allocatedOperational.ofExpression allocatedInvariant.ready catalog
    signatureFormation functionsCanonical (by simp) (by simp) baseSuccess
  have keyOperational : GeneralizedActualStateInvariant keyState (evidenceState.toTypedSource roots) := by
    simpa only [keyEq] using baseOperational.fresh
  have valueOperational : GeneralizedActualStateInvariant valueState (evidenceState.toTypedSource roots) := by
    simpa only [valueEq] using keyOperational.fresh
  have keyBinders : keyState.localBinders = baseState.localBinders := by
    rw [← keyEq]; rfl
  have valueBinders : valueState.localBinders = keyState.localBinders := by
    rw [← valueEq]; rfl
  have baseBinders : baseState.localBinders = allocated.localBinders :=
    congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq baseSuccess)
  have valueSafety : ∀ binder ∈ valueState.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified valueState baseResult.type ∧
      ProtectedVariables.Safe binder.scheme.quantified valueState (.mapping keyType valueType) ∧
      ProtectedVariables.Safe binder.scheme.quantified valueState keyType := by
    intro binder member
    have inKey := valueBinders ▸ member
    have inBase := keyBinders ▸ inKey
    have inAllocated := baseBinders ▸ inBase
    have basePrivate := ProtectedVariables.inferExprFuel_private binder.scheme.quantified childFuel
      inferenceContext baseExpression none allocated allocatedInvariant.ready allocatedOperational.requirements
      (allocatedOperational.quantifiersBelow binder inAllocated)
      (allocatedOperational.privacy binder inAllocated) catalog signatureFormation functionsCanonical
      (by simp) (by simp) _ baseSuccess
    have toKey : ProtectedVariables.SafeTransport binder.scheme.quantified baseState keyState := by
      simpa only [keyFresh] using (ProtectedVariables.fresh (protectedVars := binder.scheme.quantified) (state := baseState))
    have toValue : ProtectedVariables.SafeTransport binder.scheme.quantified keyState valueState := by
      simpa only [valueFresh] using (ProtectedVariables.fresh (protectedVars := binder.scheme.quantified) (state := keyState))
    have keySafe : ProtectedVariables.Safe binder.scheme.quantified keyState keyType := by
      simpa only [keyFresh] using ProtectedVariables.fresh_type baseInvariant.ready
        (baseOperational.quantifiersBelow binder inBase)
    have valueSafe : ProtectedVariables.Safe binder.scheme.quantified valueState valueType := by
      simpa only [valueFresh] using ProtectedVariables.fresh_type keyInvariant.ready
        (keyOperational.quantifiersBelow binder inKey)
    exact ⟨toValue _ (toKey _ basePrivate.2.1),
      (ProtectedVariables.safe_mapping_iff _ _ _ _).mpr ⟨toValue _ keySafe, valueSafe⟩,
      toValue _ keySafe⟩
  have mappingOperational := valueOperational.unify valueInvariant.ready baseAtValue mappingBelow
    (fun binder member => (valueSafety binder member).1)
    (fun binder member => (valueSafety binder member).2.1) mappingSuccess
  have indexSafe : ∀ binder ∈ mappingState.localBinders,
      ∀ type ∈ (some (mappingState.resolve keyType) : Option Ty),
      ProtectedVariables.Safe binder.scheme.quantified mappingState type := by
    intro binder member type typeMember
    have same : type = mappingState.resolve keyType := (Option.some.inj typeMember).symm
    subst type
    have binders : mappingState.localBinders = valueState.localBinders :=
      congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope mappingSuccess)
    have safe := valueSafety binder (binders ▸ member)
    exact ProtectedVariables.safe_resolved mappingReady
      (ProtectedVariables.unify safe.1 safe.2.1 mappingSuccess keyType safe.2.2)
  have indexExpected : ∀ type ∈ (some (mappingState.resolve keyType) : Option Ty),
      type.VariablesBelow mappingState.inference.next := by
    intro type member
    have same : type = mappingState.resolve keyType := (Option.some.inj member).symm
    subst type
    exact resolvedKeyBelow
  obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded roots
  have edge : ∀ child ∈ [baseResult.id, indexResult.id],
      DirectChild (resultState.toTypedSource roots) (.expression inferred.id) (.expression child) := by
    intro child member
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simpa [nodeChildIds, Node.references, ExpressionForm.references] using
      (List.mem_map.mpr ⟨child, member, rfl⟩ : NodeId.expression child ∈
        [baseResult.id, indexResult.id].map NodeId.expression)
  have baseEdge := edge baseResult.id (by simp)
  have baseHere := descend here
    (ChildStep.expression_index_base boundary.accepted expressionEq allocationEq baseSuccess)
  have baseTypeRaw := expressionRooted_of_retained_for checked recursive baseHere ({
    accepted := baseSuccess
    interfaces := boundary.interfaces
    extension := laterBase
    scope := boundary.scope
    invariant := allocatedInvariant
    actual := boundary.actual
    operational := allocatedOperational
    expectedBelow := by simp
    expectedAdmissible := by simp
    expectedSafe := by simp
    rawSubtree := (rawProper.childSubtree baseEdge).monoBefore baseToParent
    integerPatterns := List.Subset.trans baseIntegerPatternsSubset integerPatternsSubset
    integerLiterals := List.Subset.trans baseIntegerLiteralsSubset integerLiteralsSubset
    requirements := List.Subset.trans baseRequirementsSubset requirementsSubset
    covered := covered.expressionChild resources.graph_closed (boundary.directChildren baseEdge)
    actualCovered := actualCovered.directChild (boundary.directChildren baseEdge) } :
    RootedExpressionBoundary _ _ _ _ _ _ _ _ _ _)
  have unifiedEq : mappingState.resolve baseResult.type =
      mappingState.resolve (.mapping keyType valueType) := by
    simpa [Frontend.SourceInference.State.resolve] using
      Detail.unify_resolve_eq mappingSuccess
  have resolvedBaseEq :
      finalized.substitution.apply
          (mappingState.resolve baseResult.type) =
        finalized.substitution.apply baseResult.type := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterMapping baseResult.type
  have resolvedMappingEq :
      finalized.substitution.apply
          (mappingState.resolve (.mapping keyType valueType)) =
        finalized.substitution.apply (.mapping keyType valueType) := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
        laterMapping (.mapping keyType valueType)
  have baseEq : finalized.substitution.apply baseResult.type =
      .mapping (finalized.substitution.apply keyType)
        (finalized.substitution.apply valueType) := by
    calc
      finalized.substitution.apply baseResult.type =
          finalized.substitution.apply
            (mappingState.resolve baseResult.type) := resolvedBaseEq.symm
      _ = finalized.substitution.apply
          (mappingState.resolve (.mapping keyType valueType)) :=
        congrArg finalized.substitution.apply unifiedEq
      _ = finalized.substitution.apply
          (.mapping keyType valueType) := resolvedMappingEq
      _ = .mapping (finalized.substitution.apply keyType)
          (finalized.substitution.apply valueType) := rfl
  have resolvedKeyEq :
      finalized.substitution.apply (mappingState.resolve keyType) =
        finalized.substitution.apply keyType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterMapping keyType
  have indexEdge := edge indexResult.id (by simp)
  have indexHere := descend here
    (ChildStep.expression_index_key boundary.accepted expressionEq allocationEq baseSuccess
      keyFresh valueFresh mappingSuccess indexSuccess)
  have indexTypeRaw := expressionRooted_of_retained_for checked recursive indexHere ({
    accepted := indexSuccess
    interfaces := boundary.interfaces
    extension := laterIndex
    scope := boundary.scope
    invariant := mappingInvariant
    actual := boundary.actual
    operational := mappingOperational
    expectedBelow := indexExpected
    expectedAdmissible := by
      intro type member
      have same : type = mappingState.resolve keyType := (Option.some.inj member).symm
      subst type
      rw [resolvedKeyEq]
      have baseAdmissible := baseTypeRaw.type_admissible
      rw [baseEq] at baseAdmissible
      exact TypeAdmissible.mapping_key baseAdmissible
    expectedSafe := indexSafe
    rawSubtree := (rawProper.childSubtree indexEdge).monoBefore indexToParent
    integerPatterns := List.Subset.trans indexIntegerPatternsSubset integerPatternsSubset
    integerLiterals := List.Subset.trans indexIntegerLiteralsSubset integerLiteralsSubset
    requirements := List.Subset.trans indexRequirementsSubset requirementsSubset
    covered := covered.expressionChild resources.graph_closed (boundary.directChildren indexEdge)
    actualCovered := actualCovered.directChild (boundary.directChildren indexEdge) } :
    RootedExpressionBoundary _ _ _ _ _ _ _ _ _ _)
  have indexExpectedEq :
      finalized.substitution.apply indexResult.type =
        finalized.substitution.apply
          (mappingState.resolve keyType) :=
    Detail.inferExprFuel_expected_type_apply_eq indexSuccess laterIndex
  have resolvedValueEq :
      finalized.substitution.apply (indexState.resolve valueType) =
        finalized.substitution.apply valueType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterIndex valueType
  have baseType : ExpressionHasType semanticSource semanticContext baseResult.id
      (.mapping (finalized.substitution.apply keyType)
        (finalized.substitution.apply valueType)) := by
    rw [← baseEq]
    exact baseTypeRaw
  have indexType : ExpressionHasType semanticSource semanticContext indexResult.id
      (finalized.substitution.apply keyType) := by
    rw [← resolvedKeyEq, ← indexExpectedEq]
    exact indexTypeRaw
  have formType : ExpressionFormHasRawType semanticSource semanticContext
      ((ExpressionForm.index baseResult.id indexResult.id).applySubstitution
        finalized.substitution)
      (finalized.substitution.apply (indexState.resolve valueType))
      (.ordinary []) := by
    rw [resolvedValueEq]
    simpa [ExpressionForm.applySubstitution] using
      ExpressionFormHasRawType.index baseType indexType
  have rawAdmissible : TypeAdmissible semanticContext
      (finalized.substitution.apply (indexState.resolve valueType)) := by
    rw [resolvedValueEq]
    exact TypeAdmissible.mapping_value baseType.type_admissible
  exact recordExpressionWithExpected_success_expressionTypingBase_actual resources interfaces
    recorded resultSubstitutionExtension requirementsSubset boundary.expressionRequirements boundary.coercionPrimaries
    catalog signaturesEq invariant formType rawAdmissible covered

theorem expressionRetained_index
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression baseExpression indexExpression : Syntax.Expr}
    {brackets : Syntax.SourceSpan} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (expressionEq : expression.value = .index baseExpression brackets indexExpression)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  exact expressionRetained_index_for (provenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursive boundary) trivial expressionEq boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedLambdaSoundness
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend Frontend.SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

private theorem bindLambdaParameters_owner_eq
    {inferenceContext : Frontend.SourceInference.Context}
    {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String}
    {state : Frontend.SourceInference.State}
    {result : List TypedBinder × List TypeSystem.Ty ×
      Frontend.SourceInference.State}
    (success : Detail.bindLambdaParameters inferenceContext parameters index
      seen state = .ok result) :
    result.2.2.owner = state.owner := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [Detail.bindLambdaParameters] at success
      injection success with resultEq
      subst result
      rfl
  | cons parameter rest induction =>
      cases parameterValue : parameter.value with
      | error =>
          simp [Detail.bindLambdaParameters, parameterValue, bind,
            Except.bind] at success
      | inferred name =>
          simp only [Detail.bindLambdaParameters, parameterValue] at success
          simp only [bind, Except.bind] at success
          repeat' first | split at success
          all_goals try simp_all
          all_goals
            subst result
            subst_vars
            have tailOwner := induction _ _ _ (by assumption)
            exact tailOwner.trans (by
              simp_all [Frontend.SourceInference.State.fresh,
                Frontend.SourceInference.State.allocateBinder])
      | typed marker name sourceType =>
          simp only [Detail.bindLambdaParameters, parameterValue] at success
          cases typeResult : Detail.resolveSourceType inferenceContext
              sourceType with
          | error error =>
              simp [typeResult, bind, Except.bind] at success
          | ok type =>
              simp only [typeResult, bind, Except.bind] at success
              repeat' first | split at success
              all_goals try simp_all
              all_goals
                subst result
                subst_vars
                have tailOwner := induction _ _ _ (by assumption)
                exact tailOwner.trans (by
                  simp_all [Frontend.SourceInference.State.allocateBinder])

private theorem lambdaPrefixFacts_owner_eq
    {inferenceContext : Frontend.SourceInference.Context}
    {expected : Option TypeSystem.Ty}
    {returnAnnotation : Option Syntax.TypeExpr}
    {parameterTypes : List TypeSystem.Ty}
    {parameterState resultState : Frontend.SourceInference.State}
    {resultType : TypeSystem.Ty}
    (facts : Detail.LambdaPrefixFacts inferenceContext expected
      returnAnnotation parameterTypes parameterState resultType resultState) :
    resultState.owner = parameterState.owner := by
  cases facts with
  | noExpectedPartsAnnotated => rfl
  | noExpectedPartsFresh _ _ freshEq =>
      have finalEq : parameterState.fresh.2 = resultState :=
        congrArg Prod.snd freshEq
      rw [← finalEq]
      rfl
  | expectedPartsAnnotated _ parameterUnify =>
      exact congrArg (fun header : Frontend.SourceInference.State.Header =>
        header.owner) (Detail.unify_state_header parameterUnify)
  | expectedPartsInferred _ parameterUnify =>
      exact congrArg (fun header : Frontend.SourceInference.State.Header =>
        header.owner) (Detail.unify_state_header parameterUnify)

private theorem monoBinders_ambientFields
    {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner context binders types final) :
    final.signatures = context.signatures ∧ final.typeParameters = context.typeParameters ∧
      final.currentDeclaration = context.currentDeclaration ∧
      final.residualTypeVariables = context.residualTypeVariables ∧
      final.solvedRequirements = context.solvedRequirements ∧ final.assumptions = context.assumptions := by
  induction extension with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons _ head _ induction =>
    cases head
    exact induction

theorem expressionRetained_lambda_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {keyword : Syntax.SourceSpan}
    {sourceParameters : Syntax.DelimitedList Syntax.LambdaParameter}
    {returnAnnotation : Option Syntax.TypeExpr} {body : Syntax.Block} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.expression (childFuel + 1) inferenceContext expression expected initial inferred resultState))
    (expressionEq : expression.value = .lambda keyword sourceParameters returnAnnotation body)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target)
    (bodySound : ∀ {expectedReturn : Ty} {entry : State} {result : Detail.BlockResult}
        {lambdaTarget : SourceSemantics.Context},
      callProvenance (.statements childFuel {inferenceContext with loopDepth := 0}
        body.value expectedReturn entry result) →
      (∀ binder ∈ entry.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified entry expectedReturn) →
      TypeAdmissible lambdaTarget (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel { inferenceContext with loopDepth := 0 }
        body.value expectedReturn entry result frames lambdaTarget →
      StatementsConclusion selected { inferenceContext with loopDepth := 0 }
        expectedReturn result frames lambdaTarget) :
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
  have expectedAdmissible := boundary.expectedAdmissible
  have actual := boundary.actual
  have semanticPreserved := boundary.proper
  have rawProper := boundary.rawProper
  have actualCovered := boundary.actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational : GeneralizedActualStateInvariant allocated (evidenceSource selected) := by
    rw [← show initial.allocateExpressionId.2 = allocated from congrArg Prod.snd allocationEq]
    exact boundary.operational.allocateExpressionId
  have activeBinders := invariant.typeParameterBinders (by simpa [ownerEq, typeParametersEq] using canonical)
  have activeSignaturesEq := invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeParametersEq := invariant.typeParametersEq.trans typeParametersEq.symm
  have activeOwnerEq : semanticContext.currentDeclaration = some inferenceContext.scope.genericOwner := by
    rw [ownerEq]; exact invariant.declarationEq
  have activeRange := resources.substitutionRangeAdmissible activeBinders
    invariant.signatures_eq_whole invariant.typeParametersEq invariant.declarationEq invariant.residual
  obtain ⟨boundParameters, parameterTypes, parameterState, resultType,
      prefixState, bodyResult, unifiedState, restoredState, parametersSuccess,
      prefixFacts, bodySuccess, unifySuccess, restoredEq, recordSuccess⟩ :=
    Detail.inferExprFuel_success_lambda_facts expressionEq allocationEq success
  have allocationProgress : initial.InferenceProgress allocated := by
    have progress :=
      Frontend.SourceInference.State.InferenceProgress.allocateExpressionId
        initial invariant.ready.solved
    rw [allocationEq] at progress
    exact progress
  have allocatedReady : allocated.InferenceReady := by
    have nextReady :=
      Frontend.SourceInference.State.InferenceReady.allocateExpressionId invariant.ready
    rw [allocationEq] at nextReady
    exact nextReady
  have parameterProperties :=
    Detail.bindLambdaParameters_inferenceProperties allocatedReady
      parametersSuccess
  have parameterTypeBelow :
      (TypeSystem.Ty.productMany parameterTypes).VariablesBelow
        parameterState.inference.next :=
    TypeSystem.Ty.variablesBelow_productMany parameterProperties.2.2
  have expectedAtParameter : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow parameterState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      (allocationProgress.trans parameterProperties.1).next_le
  have prefixProperties := lambdaPrefixFacts_inferenceProperties prefixFacts
    parameterProperties.2.1 parameterTypeBelow expectedAtParameter
  have lambdaSignatureFormation : ProgramSignatureFormationValidated
      ({ inferenceContext with loopDepth := 0 } :
        Frontend.SourceInference.Context).signatures := by
    simpa using signatureFormation
  have lambdaFunctionsCanonical : ∀ signature ∈
      ({ inferenceContext with loopDepth := 0 } :
        Frontend.SourceInference.Context).signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes) := by
    simpa using functionsCanonical
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := { inferenceContext with loopDepth := 0 })
    prefixProperties.2.1 lambdaSignatureFormation lambdaFunctionsCanonical
      prefixProperties.2.2 bodySuccess
  have resultAtBody : resultType.VariablesBelow
      bodyResult.state.inference.next :=
    prefixProperties.2.2.weaken bodyProperties.1.next_le
  have unifiedProgress := Detail.unify_inferenceProgress
    bodyProperties.2.1.solved bodyProperties.2.2 resultAtBody unifySuccess
  have unifiedReady := Detail.unify_preserves_inferenceReady
    bodyProperties.2.1 bodyProperties.2.2 resultAtBody unifySuccess
  have restoreStep : unifiedState.InferenceProgress restoredState := by
    rw [restoredEq]
    exact Frontend.SourceInference.State.InferenceProgress.restoreLexicalScope
      unifiedState allocated.lexicalScope unifiedReady.solved
  have throughUnified : allocated.InferenceProgress unifiedState :=
    parameterProperties.1.trans
      (prefixProperties.1.trans
        (bodyProperties.1.trans unifiedProgress))
  have restoredProperties : allocated.InferenceProgress restoredState ∧
      restoredState.InferenceReady := by
    rw [restoredEq]
    exact Frontend.SourceInference.State.restoreLexicalScope_inferenceProperties
      allocatedReady throughUnified
  have parameterToRestored :
      parameterState.InferenceProgress restoredState :=
    prefixProperties.1.trans
      (bodyProperties.1.trans (unifiedProgress.trans restoreStep))
  have resultToRestored : prefixState.InferenceProgress restoredState :=
    bodyProperties.1.trans (unifiedProgress.trans restoreStep)
  have resolvedParameterBelow :
      (restoredState.resolve
        (TypeSystem.Ty.productMany parameterTypes)).VariablesBelow
          restoredState.inference.next :=
    parameterToRestored.resolve_variablesBelow parameterTypeBelow
  have resolvedResultBelow :
      (restoredState.resolve resultType).VariablesBelow
        restoredState.inference.next :=
    resultToRestored.resolve_variablesBelow prefixProperties.2.2
  have functionBelow :
      (TypeSystem.Ty.function
        (restoredState.resolve (TypeSystem.Ty.productMany parameterTypes))
        (restoredState.resolve resultType)).VariablesBelow
          restoredState.inference.next :=
    (TypeSystem.Ty.variablesBelow_function_iff _ _ _).2
      ⟨resolvedParameterBelow, resolvedResultBelow⟩
  have expectedAtRestored : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow restoredState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      (allocationProgress.trans restoredProperties.1).next_le
  have recordProperties :=
    Detail.recordExpressionWithExpected_inferenceProperties
      restoredProperties.2 functionBelow expectedAtRestored recordSuccess
  have restoredExtension : finalized.substitution.SemanticallyExtends restoredState.inference.substitution :=
    resultSubstitutionExtension.trans recordProperties.1.substitution_extends
  have parameterExtension : finalized.substitution.SemanticallyExtends parameterState.inference.substitution :=
    restoredExtension.trans parameterToRestored.substitution_extends
  have parameterTypesAdmissible :=
    bindLambdaParameters_success_typesAdmissible_in_active
      parametersSuccess canonical activeBinders activeSignaturesEq activeParametersEq
      activeOwnerEq invariant.residual activeRange
  obtain ⟨lambdaContext, namesUnique, _, parametersExtend,
      parameterInvariant, parameterBindersBelow⟩ :=
    bindLambdaParameters_success_monoBindersExtend_afterSubstitution
      parametersSuccess allocatedInvariant.active allocatedInvariant.bindersBelow
      parameterTypesAdmissible
  have sourceOwner : semanticSource.owner = allocated.owner := by
    exact semanticPreserved.owner_eq.trans ((Detail.inferExprFuel_preserves_owner success).trans
      (congrArg (fun pair : ExpressionId × State => pair.2.owner) allocationEq))
  have parametersExtendSource : MonoBindersExtend semanticSource.owner semanticContext
      (boundParameters.map
        (TypedBinder.applySubstitution finalized.substitution))
      (parameterTypes.map finalized.substitution.apply)
      lambdaContext := by
    simpa only [sourceOwner] using parametersExtend
  have resultInvariant : ActiveLocalContextInvariant prefixState
      finalized.substitution lambdaContext :=
    lambdaPrefixFacts_activeLocalContextInvariant prefixFacts
      parameterInvariant
  have allocatedNodesBelow : allocated.NodesBelowNextOccurrence := by
    have preserved :=
      Frontend.SourceInference.State.allocateExpressionId_preserves_nodesBelowNextOccurrence
        initial invariant.nodesBelow
    have finalEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rwa [finalEq] at preserved
  have parameterNodesBelow : parameterState.NodesBelowNextOccurrence :=
    (Detail.bindLambdaParameters_occurrenceBoundExtends parametersSuccess
      ).nodesBelowNextOccurrence allocatedNodesBelow
  have resultNodesBelow : prefixState.NodesBelowNextOccurrence :=
    lambdaPrefixFacts_nodesBelowNextOccurrence prefixFacts parameterNodesBelow
  have resultBindersBelow : prefixState.LocalBindersBelowNextLocal :=
    lambdaPrefixFacts_localBindersBelowNextLocal prefixFacts
      parameterBindersBelow
  have allocatedOwner : allocated.owner = initial.owner := by
    have finalEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← finalEq]
    rfl
  have parameterOwner : parameterState.owner = allocated.owner :=
    bindLambdaParameters_owner_eq parametersSuccess
  have prefixOwner : prefixState.owner = parameterState.owner :=
    lambdaPrefixFacts_owner_eq prefixFacts
  have bodyOwner : bodyResult.state.owner = prefixState.owner :=
    Detail.inferStatementsFuel_preserves_owner bodySuccess
  have bodyToResultRaw : TypingSourceExtends
      (bodyResult.state.toTypedSource roots)
      (resultState.toTypedSource roots) := by
    constructor
    · exact (Detail.inferExprFuel_preserves_owner success).trans
        (allocatedOwner.symm.trans
          (parameterOwner.symm.trans
            (prefixOwner.symm.trans bodyOwner.symm)))
    · have nodesPrefix :=
        recordExpressionWithExpected_success_nodesPrefix recordSuccess
      have unifyNodes := (Detail.unify_occurrenceState_eq unifySuccess).1
      rw [restoredEq,
        Frontend.SourceInference.State.restoreLexicalScope_nodes,
        unifyNodes] at nodesPrefix
      exact nodesPrefix
  have laterExtendsUnified : finalized.substitution.SemanticallyExtends
      unifiedState.inference.substitution := by
    have extendsRestored := restoredExtension
    rw [restoredEq] at extendsRestored
    exact extendsRestored
  have laterExtendsBody : finalized.substitution.SemanticallyExtends
      bodyResult.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterExtendsUnified
      unifiedProgress.substitution_extends
  have bodyIntegerPatternsToResult :
      bodyResult.state.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    rw [recordExpressionWithExpected_integerPatterns_eq recordSuccess,
      restoredEq]
    change origin ∈ unifiedState.integerPatterns
    rw [Detail.unify_integerPatterns unifySuccess]
    exact member
  have bodyIntegerLiteralsToResult :
      bodyResult.state.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    rw [Detail.recordExpressionWithExpected_integerLiterals_eq recordSuccess,
      restoredEq]
    change origin ∈ unifiedState.integerLiterals
    rw [Detail.unify_integerLiterals unifySuccess]
    exact member
  have bodyRequirementsToResult :
      bodyResult.state.requirements ⊆ resultState.requirements := by
    apply List.Subset.trans ?_
      (Detail.recordExpressionWithExpected_requirements_subset recordSuccess)
    rw [restoredEq]
    change bodyResult.state.requirements ⊆ unifiedState.requirements
    rw [Detail.unify_requirements_eq unifySuccess]
    exact fun _ member => member
  have bodyIntegerPatternsToEvidence :
      bodyResult.state.integerPatterns ⊆ evidenceState.integerPatterns :=
    List.Subset.trans bodyIntegerPatternsToResult integerPatternsSubset
  have bodyIntegerLiteralsToEvidence :
      bodyResult.state.integerLiterals ⊆ evidenceState.integerLiterals :=
    List.Subset.trans bodyIntegerLiteralsToResult integerLiteralsSubset
  have bodyRequirementsToEvidence :
      bodyResult.state.requirements ⊆ evidenceState.requirements :=
    List.Subset.trans bodyRequirementsToResult requirementsSubset
  obtain ⟨coercions, recordedContains⟩ :=
    recordExpressionWithExpected_success_containsExpression recordSuccess roots
  let lambdaNode : ExpressionNode := {
    id := inferred.id
    span := expression.span
    type := inferred.type
    form := .lambda boundParameters (restoredState.resolve resultType)
      bodyResult.statements
    requirements := [] ++ Detail.coercionRequirements coercions
    coercions
  }
  have containsLambda : ContainsExpression (resultState.toTypedSource roots)
      inferred.id lambdaNode := by
    simpa only [lambdaNode] using recordedContains
  have bodyEdge : ∀ statement ∈ bodyResult.statements,
      DirectChild (resultState.toTypedSource roots) (.expression inferred.id) (.statement statement) := by
    intro statement member
    refine ⟨.expression lambdaNode, ⟨containsLambda.1, congrArg NodeId.expression containsLambda.2⟩, ?_⟩
    simpa [lambdaNode, nodeChildIds, Node.references, ExpressionForm.references] using
      (List.mem_map.mpr ⟨statement, member, rfl⟩ : (.statement statement : NodeId) ∈ bodyResult.statements.map NodeId.statement)
  have bodyCovered : ∀ statement ∈ bodyResult.statements,
      TemplateScopeCovered finalized.typedSource lambdaContext (.statement statement) := by
    intro statement member
    apply TemplateScopeCovered.expressionStatementChild covered resources.graph_closed
      (boundary.directChildren (bodyEdge statement member))
    intro predicate predicateMember
    rw [MonoBindersExtend.assumptions_eq parametersExtendSource]
    exact predicateMember
  have parameterScope := bindLambdaParameters_preserves_generalizedScope allocatedReady
    allocatedOperational allocatedInvariant.schemeIsolation parametersSuccess
  have allocatedExpectedSafe : ∀ binder ∈ allocated.localBinders, ∀ type ∈ expected,
      ProtectedVariables.Safe binder.scheme.quantified allocated type := by
    rw [← show initial.allocateExpressionId.2 = allocated from congrArg Prod.snd allocationEq]
    exact boundary.expectedSafe
  have parameterPrivacy : ∀ binder ∈ parameterState.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified parameterState (Ty.productMany parameterTypes) ∧
      (∀ type ∈ expected, ProtectedVariables.Safe binder.scheme.quantified parameterState type) := by
    intro binder member
    rcases bindLambdaParameters_quantified_origin parametersSuccess binder member with old | empty
    · have privateTypes := ProtectedVariables.bindLambdaParameters_private allocatedReady
        (allocatedOperational.quantifiersBelow binder old) (allocatedOperational.privacy binder old)
        parametersSuccess
      exact ⟨ProtectedVariables.safe_productMany _ _ _ privateTypes.2.1,
        fun type present => privateTypes.1 type (allocatedExpectedSafe binder old type present)⟩
    · rw [empty]
      simp [ProtectedVariables.Safe, ProtectedVariables.Avoids]
  have prefixScope := lambdaPrefixFacts_preserves_generalizedScope parameterProperties.2.1
    parameterScope.1 parameterScope.2 parameterTypeBelow
    (fun binder member => (parameterPrivacy binder member).1) expectedAtParameter
    (fun binder member => (parameterPrivacy binder member).2) prefixFacts
  have lambdaFields : lambdaContext.signatures = semanticContext.signatures ∧
      lambdaContext.typeParameters = semanticContext.typeParameters ∧
      lambdaContext.currentDeclaration = semanticContext.currentDeclaration ∧
      lambdaContext.residualTypeVariables = semanticContext.residualTypeVariables ∧
      lambdaContext.solvedRequirements = semanticContext.solvedRequirements ∧
      lambdaContext.assumptions = semanticContext.assumptions := monoBinders_ambientFields parametersExtend
  have prefixInvariant : RecursiveStatementInvariant wholeContext resultType finalized prefixState lambdaContext := {
    active := resultInvariant
    ready := prefixProperties.2.1
    returnBelow := prefixProperties.2.2
    bindersBelow := resultBindersBelow
    nodesBelow := resultNodesBelow
    schemeIsolation := prefixScope.2.1
    substitutionExtension := laterExtendsBody.trans bodyProperties.1.substitution_extends
    signaturesEq := lambdaFields.1.trans invariant.signaturesEq
    typeParametersEq := lambdaFields.2.1.trans invariant.typeParametersEq
    declarationEq := lambdaFields.2.2.1.trans invariant.declarationEq
    residual := lambdaFields.2.2.2.1.trans invariant.residual
    solvedRequirementsEq := lambdaFields.2.2.2.2.1.trans invariant.solvedRequirementsEq
    assumptionsMono := by rw [lambdaFields.2.2.2.2.2]; exact invariant.assumptionsMono
  }
  have resultAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply resultType) :=
    lambdaPrefixFacts_resultTypeAdmissible_in_active prefixFacts canonical activeBinders
      activeSignaturesEq activeParametersEq activeOwnerEq invariant.residual activeRange
      parameterExtension expectedAdmissible
  have lambdaReturnAdmissible : TypeAdmissible lambdaContext (finalized.substitution.apply resultType) := by
    apply StructuralSubstitution.TypeAdmissible.transportContext (source := semanticContext)
    · exact lambdaFields.1
    · exact lambdaFields.2.1
    · exact lambdaFields.2.2.1
    · exact (actual.monoBinders parametersExtend).variables_eq.trans actual.variables_eq.symm
    · exact lambdaFields.2.2.2.1
    · exact resultAdmissible
  obtain ⟨bodyFinal, bodyFacts, _, _, _, bodyType, bodyAgreement⟩ :=
    bodySound (descend here (.expression_lambda_body success expressionEq allocationEq
      parametersSuccess prefixFacts bodySuccess)) prefixScope.2.2 lambdaReturnAdmissible ({
      accepted := bodySuccess
      interfaces := boundary.interfaces
      extension := laterExtendsBody
      scope := boundary.scope.withLoopDepth 0
      invariant := prefixInvariant
      actual := actual.monoBinders parametersExtend
      operational := prefixScope.1
      rawSubtrees := fun statement member =>
        (rawProper.childSubtree (bodyEdge statement member)).monoBefore bodyToResultRaw
      integerPatterns := bodyIntegerPatternsToEvidence
      integerLiterals := bodyIntegerLiteralsToEvidence
      requirements := bodyRequirementsToEvidence
      covered := bodyCovered
      actualCovered := fun statement member =>
        actualCovered.directChild (boundary.directChildren (bodyEdge statement member)) } :
      StatementsBoundary selected childFuel { inferenceContext with loopDepth := 0 }
        body.value resultType prefixState bodyResult frames lambdaContext)
  have unifiedTypesEq : finalized.substitution.apply bodyResult.type =
      finalized.substitution.apply resultType := by
    calc
      finalized.substitution.apply bodyResult.type =
          finalized.substitution.apply
            (unifiedState.resolve bodyResult.type) := by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using
            (laterExtendsUnified bodyResult.type).symm
      _ = finalized.substitution.apply
          (unifiedState.resolve resultType) :=
        congrArg finalized.substitution.apply
          (Detail.unify_resolve_eq unifySuccess)
      _ = finalized.substitution.apply resultType := by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using
            laterExtendsUnified resultType
  have bodyFactsType : bodyFacts.type =
      finalized.substitution.apply resultType :=
    bodyAgreement.type_eq.trans unifiedTypesEq
  have bodyCompletes : BodyCompletes
      (finalized.substitution.apply resultType) bodyFacts :=
    bodyType.bodyCompletes_of_closed rfl bodyFactsType
  have parameterResolved :
      finalized.substitution.apply
          (restoredState.resolve (TypeSystem.Ty.productMany parameterTypes)) =
        TypeSystem.Ty.productMany
          (parameterTypes.map finalized.substitution.apply) := by
    calc
      finalized.substitution.apply
          (restoredState.resolve (TypeSystem.Ty.productMany parameterTypes)) =
          finalized.substitution.apply
            (TypeSystem.Ty.productMany parameterTypes) := by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using
            restoredExtension
              (TypeSystem.Ty.productMany parameterTypes)
      _ = TypeSystem.Ty.productMany
          (parameterTypes.map finalized.substitution.apply) := by
        exact FlexibleSubstitution.apply_productMany _ _
  have resultResolved :
      finalized.substitution.apply (restoredState.resolve resultType) =
        finalized.substitution.apply resultType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
        restoredExtension resultType
  have formType : ExpressionFormHasRawType semanticSource semanticContext
      ((ExpressionForm.lambda boundParameters (restoredState.resolve resultType)
        bodyResult.statements).applySubstitution finalized.substitution)
      (finalized.substitution.apply
        (.function
          (restoredState.resolve (TypeSystem.Ty.productMany parameterTypes))
          (restoredState.resolve resultType)))
      (.ordinary []) := by
    rw [show finalized.substitution.apply
          (.function
            (restoredState.resolve (TypeSystem.Ty.productMany parameterTypes))
            (restoredState.resolve resultType)) =
        .function
          (TypeSystem.Ty.productMany
            (parameterTypes.map finalized.substitution.apply))
          (finalized.substitution.apply resultType) by
      simp only [FlexibleSubstitution.apply_function, parameterResolved,
        resultResolved]]
    simpa [ExpressionForm.applySubstitution, resultResolved] using
      (ExpressionFormHasRawType.lambda
        (source := semanticSource)
        (by simpa [List.map_map, Function.comp_def,
          TypedBinder.applySubstitution] using namesUnique)
        parametersExtendSource bodyType bodyCompletes)
  have rawAdmissible : TypeAdmissible semanticContext
      (finalized.substitution.apply
        (.function
          (restoredState.resolve (TypeSystem.Ty.productMany parameterTypes))
          (restoredState.resolve resultType))) := by
    rw [show finalized.substitution.apply
          (.function
            (restoredState.resolve (TypeSystem.Ty.productMany parameterTypes))
            (restoredState.resolve resultType)) =
        .function
          (TypeSystem.Ty.productMany
            (parameterTypes.map finalized.substitution.apply))
          (finalized.substitution.apply resultType) by
      simp only [FlexibleSubstitution.apply_function, parameterResolved,
        resultResolved]]
    exact TypeAdmissible.function
      (parametersExtendSource.product_type_admissible activeBinders)
      resultAdmissible
  exact recordExpressionWithExpected_success_expressionTypingBase_actual resources interfaces
    recordSuccess resultSubstitutionExtension requirementsSubset boundary.expressionRequirements boundary.coercionPrimaries
    catalog signaturesEq invariant formType rawAdmissible covered

theorem expressionRetained_lambda
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {keyword : Syntax.SourceSpan}
    {sourceParameters : Syntax.DelimitedList Syntax.LambdaParameter}
    {returnAnnotation : Option Syntax.TypeExpr} {body : Syntax.Block} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (expressionEq : expression.value = .lambda keyword sourceParameters returnAnnotation body)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target)
    (bodySound : ∀ {expectedReturn : Ty} {entry : State} {result : Detail.BlockResult}
        {lambdaTarget : SourceSemantics.Context},
      (∀ binder ∈ entry.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified entry expectedReturn) →
      TypeAdmissible lambdaTarget (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel { inferenceContext with loopDepth := 0 }
        body.value expectedReturn entry result frames lambdaTarget →
      StatementsConclusion selected { inferenceContext with loopDepth := 0 }
        expectedReturn result frames lambdaTarget) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  exact expressionRetained_lambda_for (callProvenance := fun _ => True) checked true_childClosed
    True.intro expressionEq boundary (fun _ safe admissible boundary => bodySound safe admissible boundary)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionDispatch
/-! Expression dispatch uses smaller actual expression calls and the statement
family at the lambda body's fuel. Lambda entry supplies the concrete return
privacy and admissibility conditions from its actual parameter prefix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}

def StatementsRootedSoundness (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.BlockResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    (∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn) →
    TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
    StatementsBoundary selected childFuel inferenceContext statements expectedReturn
      initial result frames target →
    StatementsConclusion selected inferenceContext expectedReturn result frames target

theorem expressionRetained_zero : ExpressionRetainedSoundness selected 0 := by
  intro inferenceContext expression expected initial resultState inferred frames target boundary
  have success := boundary.accepted
  simp only [Detail.inferExprFuel] at success
  cases success

theorem expressionRetained_step_for {callProvenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    (bodySound : StatementsRootedSoundnessFor callProvenance selected childFuel) :
    ExpressionRetainedSoundnessFor callProvenance selected (childFuel + 1) := by
  intro inferenceContext expression expected initial resultState inferred frames target here boundary
  have predecessor : ExpressionRetainedSoundnessFor callProvenance selected childFuel :=
    recursive childFuel (Nat.lt_succ_self childFuel)
  cases form : expression.value with
  | literal literal =>
      exact expressionRetained_literal checked form boundary
  | identifier name =>
      exact expressionRetained_identifier checked form boundary
  | proxy marker type =>
      exact expressionRetained_proxy checked form boundary
  | group inner =>
      exact expressionRetained_group_for checked descend predecessor here form boundary
  | tuple elements =>
      exact expressionRetained_tuple_for checked descend recursive here form boundary
  | unary operator operand =>
      exact expressionRetained_unary_for checked descend recursive here form boundary
  | binary left operator right =>
      exact expressionRetained_binary_for checked descend predecessor here form boundary
  | conditional condition question thenBranch colon elseBranch =>
      exact expressionRetained_conditional_for checked descend predecessor here form boundary
  | index base brackets index =>
      exact expressionRetained_index_for checked descend predecessor here form boundary
  | lambda keyword parameters returnAnnotation body =>
      exact expressionRetained_lambda_for checked descend here form boundary
        (fun bodyHere safe admissible bodyBoundary => bodySound bodyHere safe admissible bodyBoundary)
  | call callee arguments =>
      exact expressionRetained_call_for checked descend recursive here form boundary
  | dotConstructor dot name arguments =>
      exact constructor_dot_for checked descend predecessor here form boundary
  | field base dot name =>
      exact constructor_field_for checked descend predecessor here form boundary
  | array elements =>
      have success := boundary.accepted
      simp only [Detail.inferExprFuel, form] at success
      cases success
  | error =>
      have success := boundary.accepted
      simp only [Detail.inferExprFuel, form] at success
      cases success

theorem expressionRetained_step
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    (bodySound : StatementsRootedSoundness selected childFuel) :
    ExpressionRetainedSoundness selected (childFuel + 1) := by
  exact expressionRetained_step_for (callProvenance := fun _ => True) checked true_childClosed
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursive smaller less boundary)
    (fun _ safe admissible boundary => bodySound safe admissible boundary) True.intro

theorem expressionRooted_zero
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ExpressionRootedSoundness selected 0 :=
  expressionRooted_of_retained checked expressionRetained_zero

theorem expressionRooted_step
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    (bodySound : StatementsRootedSoundness selected childFuel) :
    ExpressionRootedSoundness selected (childFuel + 1) :=
  expressionRooted_of_retained checked (expressionRetained_step checked recursive bodySound)


theorem expressionRetained_zero_for {callProvenance : CallIndex → Prop} :
    ExpressionRetainedSoundnessFor callProvenance selected 0 := by
  intro context source expected initial final value frames target _ boundary
  exact expressionRetained_zero boundary

theorem expressionRooted_zero_for {callProvenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ExpressionRootedSoundnessFor callProvenance selected 0 := by
  intro context source expected initial final value frames target here boundary
  exact expressionRooted_of_retained_for checked expressionRetained_zero_for here boundary

theorem expressionRooted_step_for {callProvenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    (bodySound : StatementsRootedSoundnessFor callProvenance selected childFuel) :
    ExpressionRootedSoundnessFor callProvenance selected (childFuel + 1) := by
  intro context source expected initial final value frames target here boundary
  exact expressionRooted_of_retained_for checked
    (expressionRetained_step_for checked descend recursive bodySound) here boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedAssemblyContracts
/-! The recursive assembly uses the original selected function throughout.
Its remaining generalization inputs concern concrete initializer occurrences
and their actual semantic boundaries. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

def StatementRootedSoundness (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    (∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn) →
    TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
    StatementBoundary selected childFuel inferenceContext statement expectedReturn
      initial result frames target →
    StatementConclusion selected inferenceContext expectedReturn result frames target

structure BodyInitializerBarriers (selected : BodySelection compiled row fuel) : Prop where
  statement : ∀ {source : Syntax.Statement} {expectedReturn : Ty}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
      (occurrence : BodyInitializerOccurrence selected source),
    StatementBoundary selected (occurrence.childFuel + 1) occurrence.inferenceContext source expectedReturn
      occurrence.entry occurrence.result frames target →
    GeneralizationBarrierTransport occurrence.receipt.ready occurrence.receipt.locals
      occurrence.entry.nextRequirement (occurrence.receipt.ready.resolve occurrence.receipt.value.type)
      selected.body.finalized.substitution target (localSchemeTemplateIds occurrence.initializerBinding.binder)
  header : ∀ {childFuel : Nat} {inferenceContext : SourceInference.Context} {item : Syntax.ForItem}
      {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target →
    ∀ receipt : LocalHeaderRequirementTiming.Receipt childFuel inferenceContext item initial (inferred, final),
    GeneralizationBarrierTransport receipt.ready receipt.locals initial.nextRequirement
      (receipt.ready.resolve receipt.value.type) selected.body.finalized.substitution target
      (localSchemeTemplateIds (receipt.binding.1.applySubstitution selected.body.finalized.substitution))

/-- The ordinary API retains its original Selected argument. -/
abbrev SelectedInitializerBarriers (selected : Selected compiled row fuel) : Prop :=
  BodyInitializerBarriers selected.toBodySelection

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedPlaceSoundness
/-! Writable places and their mapping keys use the same selected final source.
Every recursive key boundary comes from the actual place traversal. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel}

theorem placeRootedSoundness_for
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed provenance) :
    ∀ childFuel, (∀ smaller, smaller < childFuel → ExpressionRootedSoundnessFor provenance selected smaller) →
      PlaceRootedSoundnessFor provenance selected childFuel := by
  intro childFuel
  induction childFuel with
  | zero =>
      intro _ inferenceContext expression initial final place frames target _here boundary
      have success := boundary.accepted
      simp only [Detail.inferPlaceFuel] at success
      cases success
  | succ childFuel induction =>
      intro expressionSound inferenceContext expression initial final place frames target here boundary
      have formation := boundary.scope.formation checked
      have canonical := boundary.scope.functionsCanonical checked
      have catalog := boundary.scope.catalog checked
      refine ⟨?_, boundary.operational.ofPlace boundary.invariant.ready catalog formation canonical boundary.accepted,
        boundary.operational.place_type_private boundary.invariant.ready catalog formation canonical boundary.accepted⟩
      cases form : expression.value
      case identifier name =>
        rw [selected.body.resources.source_eq]
        exact inferPlaceFuel_success_identifier_sound form boundary.accepted
          boundary.invariant.active boundary.extension
      case group inner =>
        have childSuccess : Detail.inferPlaceFuel childFuel inferenceContext inner initial = .ok (place, final) := by
          simpa only [Detail.inferPlaceFuel, form] using boundary.accepted
        exact (induction (fun smaller below => expressionSound smaller
          (Nat.lt_trans below (Nat.lt_succ_self childFuel)))
          (descend here (ChildStep.place_group boundary.accepted form childSuccess))
          { boundary with accepted := childSuccess }).1
      case index base brackets key =>
        obtain ⟨basePlace, baseState, keyInitial, inferredKey, baseSuccess,
            baseInvariant, unifySuccess, keySuccess, placeEq, keyInvariant,
            keyExpectedBelow, keyMember⟩ :=
          inferPlaceFuel_index_key_invariant form boundary.accepted formation canonical
            boundary.invariant boundary.extension
        obtain ⟨actualPlace, actualState, actualSuccess, _baseBelow, baseToFinal,
            baseLiterals, basePatterns, baseRequirements⟩ :=
          inferPlaceFuel_success_index_base_state_provenance form boundary.accepted
            boundary.invariant.nodesBelow (bodyRoots selected)
        rw [baseSuccess] at actualSuccess
        obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualSuccess).symm
        have baseReferences : ∀ keyId, .expression keyId ∈ basePlace.references →
            .expression keyId ∈ place.references := by
          intro keyId member
          exact inferPlaceFuel_index_base_references_subset form baseSuccess boundary.accepted member
        have baseTyped := (induction (fun smaller below => expressionSound smaller
          (Nat.lt_trans below (Nat.lt_succ_self childFuel)))
          (descend here (ChildStep.place_index_base boundary.accepted form baseSuccess)) ({
            accepted := baseSuccess
            interfaces := boundary.interfaces
            extension := baseInvariant.substitutionExtension
            scope := boundary.scope
            invariant := boundary.invariant
            actual := boundary.actual
            operational := boundary.operational
            rawKeys := fun keyId member => (boundary.rawKeys keyId (baseReferences keyId member)).monoBefore baseToFinal
            integerPatterns := List.Subset.trans basePatterns boundary.integerPatterns
            integerLiterals := List.Subset.trans baseLiterals boundary.integerLiterals
            requirements := List.Subset.trans baseRequirements boundary.requirements
            covered := fun keyId member => boundary.covered keyId (baseReferences keyId member)
            actualCovered := fun keyId member => boundary.actualCovered keyId (baseReferences keyId member)
          } : PlaceBoundary selected childFuel inferenceContext base initial basePlace baseState frames target)).1
        obtain ⟨keyOperational, keySafe⟩ := boundary.operational.placeIndexPrefix boundary.invariant.ready
          catalog formation canonical baseSuccess unifySuccess
        have baseEq : selected.body.finalized.substitution.apply basePlace.type =
            .mapping (selected.body.finalized.substitution.apply baseState.fresh.1)
              (selected.body.finalized.substitution.apply baseState.fresh.2.fresh.1) := by
          calc
            selected.body.finalized.substitution.apply basePlace.type =
                selected.body.finalized.substitution.apply (keyInitial.resolve basePlace.type) := by
              simpa only [State.resolve, InferState.resolve] using
                (keyInvariant.substitutionExtension basePlace.type).symm
            _ = selected.body.finalized.substitution.apply
                (keyInitial.resolve (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1)) :=
              congrArg selected.body.finalized.substitution.apply (Detail.unify_resolve_eq unifySuccess)
            _ = .mapping (selected.body.finalized.substitution.apply baseState.fresh.1)
                  (selected.body.finalized.substitution.apply baseState.fresh.2.fresh.1) := by
              simpa only [State.resolve, InferState.resolve, Substitution.apply] using
                keyInvariant.substitutionExtension (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1)
        have expectedEq : selected.body.finalized.substitution.apply (keyInitial.resolve baseState.fresh.1) =
            selected.body.finalized.substitution.apply baseState.fresh.1 := by
          simpa only [State.resolve, InferState.resolve] using keyInvariant.substitutionExtension baseState.fresh.1
        have keyTyped := expressionSound childFuel (Nat.lt_succ_self childFuel)
          (descend here (ChildStep.place_index_key boundary.accepted form baseSuccess rfl rfl
            unifySuccess keySuccess)) ({
          accepted := keySuccess
          interfaces := boundary.interfaces
          extension := boundary.extension
          scope := boundary.scope
          invariant := keyInvariant
          actual := boundary.actual
          operational := keyOperational
          expectedBelow := by
            intro type member
            have same : type = keyInitial.resolve baseState.fresh.1 := (Option.some.inj member).symm
            subst type
            exact keyExpectedBelow
          expectedAdmissible := by
            intro type member
            have same : type = keyInitial.resolve baseState.fresh.1 := (Option.some.inj member).symm
            subst type
            rw [expectedEq]
            have valid := sourcePlace_type_admissible baseTyped
            rw [baseEq] at valid
            exact TypeAdmissible.mapping_key valid
          expectedSafe := by
            intro binder member type typeMember
            have same : type = keyInitial.resolve baseState.fresh.1 := (Option.some.inj typeMember).symm
            subst type
            exact keySafe binder member
          rawSubtree := boundary.rawKeys inferredKey.id keyMember
          integerPatterns := boundary.integerPatterns
          integerLiterals := boundary.integerLiterals
          requirements := boundary.requirements
          covered := boundary.covered inferredKey.id keyMember
          actualCovered := boundary.actualCovered inferredKey.id keyMember
        } : RootedExpressionBoundary selected childFuel inferenceContext key
          (some (keyInitial.resolve baseState.fresh.1)) keyInitial inferredKey final frames target)
        rw [selected.body.resources.source_eq] at baseTyped keyTyped ⊢
        exact inferPlaceFuel_index_sound_of_actual_typed_children baseSuccess unifySuccess keySuccess placeEq
          keyInvariant.substitutionExtension boundary.extension baseTyped keyTyped
      all_goals
        have success := boundary.accepted
        simp [Detail.inferPlaceFuel, form] at success

theorem placeRootedSoundness
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ∀ childFuel, (∀ smaller, smaller < childFuel → ExpressionRootedSoundness selected smaller) →
      PlaceRootedSoundness selected childFuel := by
  intro childFuel expressionSound
  have recursiveFor (smaller : Nat) (below : smaller < childFuel) :
      ExpressionRootedSoundnessFor (fun _ => True) selected smaller :=
    fun _ boundary => expressionSound smaller below boundary
  intro inferenceContext expression initial final place frames target boundary
  exact placeRootedSoundness_for (provenance := fun _ => True) checked
    true_childClosed childFuel recursiveFor
    trivial boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledProvenanceCompatibility
/-! The original APIs are exactly the unrestricted instance of call provenance.
The conversion does not construct provenance for any actual selected run. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}

theorem statementRootedSoundnessFor_true
    (sound : StatementRootedSoundness selected childFuel) :
    StatementRootedSoundnessFor (fun _ => True) selected childFuel :=
  fun _ safe admissible boundary => sound safe admissible boundary

theorem statementRootedSoundness_of_true
    (sound : StatementRootedSoundnessFor (fun _ => True) selected childFuel) :
    StatementRootedSoundness selected childFuel :=
  fun safe admissible boundary => sound trivial safe admissible boundary

theorem statementsRootedSoundnessFor_true
    (sound : StatementsRootedSoundness selected childFuel) :
    StatementsRootedSoundnessFor (fun _ => True) selected childFuel :=
  fun _ safe admissible boundary => sound safe admissible boundary

theorem statementsRootedSoundness_of_true
    (sound : StatementsRootedSoundnessFor (fun _ => True) selected childFuel) :
    StatementsRootedSoundness selected childFuel :=
  fun safe admissible boundary => sound trivial safe admissible boundary

theorem forItemRootedSoundnessFor_true
    (sound : ForItemRootedSoundness selected childFuel) :
    ForItemRootedSoundnessFor (fun _ => True) selected childFuel :=
  fun _ boundary => sound boundary

theorem forItemRootedSoundness_of_true
    (sound : ForItemRootedSoundnessFor (fun _ => True) selected childFuel) :
    ForItemRootedSoundness selected childFuel :=
  fun boundary => sound trivial boundary

theorem forItemsRootedSoundnessFor_true
    (sound : ForItemsRootedSoundness selected childFuel) :
    ForItemsRootedSoundnessFor (fun _ => True) selected childFuel :=
  fun _ boundary => sound boundary

theorem forItemsRootedSoundness_of_true
    (sound : ForItemsRootedSoundnessFor (fun _ => True) selected childFuel) :
    ForItemsRootedSoundness selected childFuel :=
  fun boundary => sound trivial boundary

theorem placeRootedSoundnessFor_true
    (sound : PlaceRootedSoundness selected childFuel) :
    PlaceRootedSoundnessFor (fun _ => True) selected childFuel :=
  fun _ boundary => sound boundary

theorem placeRootedSoundness_of_true
    (sound : PlaceRootedSoundnessFor (fun _ => True) selected childFuel) :
    PlaceRootedSoundness selected childFuel :=
  fun boundary => sound trivial boundary

theorem BodyInitializerBarriers.with_true (barriers : BodyInitializerBarriers selected) :
    BodyInitializerBarriersFor (fun _ => True) selected where
  statement occurrence _ boundary := barriers.statement occurrence boundary
  header _ boundary receipt := barriers.header boundary receipt

theorem BodyInitializerBarriersFor.of_true
    (barriers : BodyInitializerBarriersFor (fun _ => True) selected) :
    BodyInitializerBarriers selected where
  statement occurrence boundary := barriers.statement occurrence trivial boundary
  header boundary receipt := barriers.header trivial boundary receipt

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end
