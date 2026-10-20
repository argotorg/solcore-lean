import Solcore.SourceSemantics.SourceCompiledProvenanceExpressionContracts
import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedUnarySoundness
import Solcore.SourceSemantics.SourceInferenceSelectedBinarySoundness

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
