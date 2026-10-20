import Solcore.SourceSemantics.SourceInferenceNormalizedLookupBranch
import Solcore.SourceSemantics.SourceInferenceNormalizedOperatorIssuance
import Solcore.SourceSemantics.SourceInferenceNormalizedInitializedContinuation
import Solcore.SourceSemantics.SourceInferenceNormalizedConstructorContinuation
import Solcore.SourceSemantics.SourceInferenceNormalizedRecordingContinuation
import Solcore.SourceSemantics.SourceInferenceNormalizedPatternFormation
import Solcore.SourceSemantics.SourceInferenceNormalizedLambdaContinuation
import Solcore.SourceSemantics.SourceInferenceNormalizedMatchContinuation
import Solcore.SourceSemantics.SourceInferenceNormalizedCallFormation
import Solcore.SourceSemantics.SourceInferenceNormalizedOperatorContinuation
import Solcore.SourceSemantics.SourceInferenceNormalizedCallContinuation
import Solcore.SourceSemantics.SourceInferenceNormalizedIndexContinuation
import Solcore.SourceSemantics.SourceInferenceNormalizedForContinuation
import Solcore.SourceSemantics.SourceInferenceNormalizedOperatorBranches

/-! Final normalized formation through the actual recursive source inference.
The final substitution and capture checks come from the eventual real finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceRequirementFormation

private theorem expression_state_from_rows
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {before : State} {result : InferredExpression × State}
    (initial : NormalizedStateFormation semantic outer before)
    (accepted : inferExprFuel fuel context source expected before = .ok result)
    (issued : ∀ row ∈ result.2.requirements, row ∉ before.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate)) :
    NormalizedStateFormation semantic outer result.2 :=
  initial.of_new_rows (congrArg LexicalScope.binders
    (inferExprFuel_success_lexicalScope_eq accepted)) issued

set_option maxHeartbeats 2000000 in
private theorem inferFuel_formation_internal (semantic : SourceSemantics.Context) (outer : Substitution) :
    (∀ fuel context expression expected state,
      InferExprFuelFormation semantic outer fuel context expression expected state) ∧
    (∀ fuel context source id instantiation arguments expected state,
      InferConstructorApplicationFuelFormation semantic outer fuel context source id
        instantiation arguments expected state) ∧
    (∀ fuel context sources expected state,
      InferConstructorArgumentsFuelFormation semantic outer fuel context sources
        expected state) ∧
    (∀ fuel context statements expectedReturn state,
      InferStatementsFuelFormation semantic outer fuel context statements
        expectedReturn state) ∧
    (∀ fuel context statement expectedReturn state,
      InferStatementFuelFormation semantic outer fuel context statement
        expectedReturn state) ∧
    (∀ fuel context items state,
      InferForItemsFuelFormation semantic outer fuel context items state) ∧
    (∀ fuel context item state,
      InferForItemFuelFormation semantic outer fuel context item state) ∧
    (∀ fuel context target state,
      InferPlaceFuelFormation semantic outer fuel context target state) ∧
    (∀ fuel context target operator value state,
      InferAssignedValueFuelFormation semantic outer fuel context target operator
        value state) ∧
    (∀ fuel context expressions state,
      InferExprsFuelFormation semantic outer fuel context expressions state) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      InferMatchCasesFuelFormation semantic outer fuel context scrutineeType
        expectedReturn outerScope cases state) := by
  apply inferExprFuel.mutual_induct
    (motive1 := InferExprFuelFormation semantic outer)
    (motive2 := InferConstructorApplicationFuelFormation semantic outer)
    (motive3 := InferConstructorArgumentsFuelFormation semantic outer)
    (motive4 := InferStatementsFuelFormation semantic outer)
    (motive5 := InferStatementFuelFormation semantic outer)
    (motive6 := InferForItemsFuelFormation semantic outer)
    (motive7 := InferForItemFuelFormation semantic outer)
    (motive8 := InferPlaceFuelFormation semantic outer)
    (motive9 := InferAssignedValueFuelFormation semantic outer)
    (motive10 := InferExprsFuelFormation semantic outer)
    (motive11 := InferMatchCasesFuelFormation semantic outer)
  case case1 =>
    simp [InferExprFuelFormation, inferExprFuel]
  case case3 =>
    simp_all [InferExprFuelFormation, inferExprFuel, bind,
      Except.bind]
  case case5 =>
    simp_all [InferExprFuelFormation, inferExprFuel, bind,
      Except.bind]
  case case6 =>
    simp_all [InferExprFuelFormation, inferExprFuel]

  case case21 =>
    simp_all [InferExprFuelFormation, inferExprFuel]
  case case22 =>
    simp_all [InferExprFuelFormation, inferExprFuel]
  case case24 =>
    simp_all [InferConstructorApplicationFuelFormation,
      inferConstructorApplicationFuel, bind, Except.bind]
  case case27 =>
    simp_all [InferConstructorArgumentsFuelFormation,
      inferConstructorArgumentsFuel]
  case case28 =>
    simp [InferStatementsFuelFormation, inferStatementsFuel]
  case case31 =>
    simp [InferStatementFuelFormation, inferStatementFuel]
  case case32 =>
    simp_all [InferStatementFuelFormation, inferStatementFuel,
      bind, Except.bind]
  case case47 =>
    simp_all [InferStatementFuelFormation, inferStatementFuel]
  case case48 =>
    simp_all [InferStatementFuelFormation, inferStatementFuel]
  case case50 =>
    simp_all [InferStatementFuelFormation, inferStatementFuel]
  case case52 =>
    simp_all [InferStatementFuelFormation, inferStatementFuel]
  case case55 =>
    simp [InferForItemFuelFormation, inferForItemFuel]
  case case56 =>
    simp_all [InferForItemFuelFormation, inferForItemFuel, bind,
      Except.bind]
  case case63 =>
    simp [InferPlaceFuelFormation, inferPlaceFuel]
  case case65 =>
    simp_all [InferPlaceFuelFormation, inferPlaceFuel]
  case case66 =>
    simp_all [InferPlaceFuelFormation, inferPlaceFuel]
  case case69 =>
    simp_all [InferPlaceFuelFormation, inferPlaceFuel]
  case case71 =>
    simp [InferExprsFuelFormation, inferExprsFuel]
  case case74 =>
    simp [InferMatchCasesFuelFormation, inferMatchCasesFuel]
  case case2 =>
    intros context expression expected initial fuel id allocated allocationEq
      literal expressionEq spelling literalEq rawValue numericEq
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have produced := inferExprFuel_numeric_normalized_formation formation.toFormationContext
      formation.scope.binders expressionEq literalEq numericEq allocationEq expectedFormed continuation success
    exact ⟨produced.1, expression_state_from_rows formed success produced.2⟩
  case case4 =>
    intros context expression expected initial fuel id allocated allocationEq
      literal expressionEq spelling literalEq rawValue numericEq
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have produced := inferExprFuel_numeric_normalized_formation formation.toFormationContext
      formation.scope.binders expressionEq literalEq numericEq allocationEq expectedFormed continuation success
    exact ⟨produced.1, expression_state_from_rows formed success produced.2⟩
  case case7 =>
    intros context expression expected initial fuel id allocated allocationEq
      name expressionEq binder lookupEq localSchemeInstantiationStart
      instantiated inference advanced predicates requirements recorded requirementsEq
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    exact inferExprFuel_local_normalized_state formation ready formed expressionEq allocationEq
      lookupEq expectedBelow expectedFormed success continuation
  case case8 =>
    intros context expression expected initial fuel id allocated allocationEq
      name expressionEq lookupNone isBoolean
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have produced := inferExprFuel_boolean_normalized_formation formation.toFormationContext
      formation.scope.binders expressionEq allocationEq lookupNone isBoolean expectedFormed continuation success
    exact ⟨produced.1, expression_state_from_rows formed success produced.2⟩
  case case9 =>
    intros context expression expected initial fuel id allocated allocationEq
      name expressionEq lookupNone notBool
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have original := success
    have notBoolean : (name.value == "true" || name.value == "false") = false := by simpa using notBool
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, lookupNone, notBool, bind, Except.bind] at success
    cases functionsResult : functionsNamed context name.value with
    | error error => simp [functionsResult] at success
    | ok candidates =>
      simp only [functionsResult] at success
      cases candidates with
      | nil =>
        cases builtinResult : builtinFunctionNamed? name.value with
        | none => simp [builtinResult] at success
        | some function =>
          have produced := inferExprFuel_builtin_normalized_formation formation.toFormationContext
            formation.scope.binders expressionEq allocationEq lookupNone notBoolean functionsResult builtinResult
            expectedFormed continuation original
          exact ⟨produced.1, expression_state_from_rows formed original produced.2⟩
      | cons signature rest =>
        cases rest with
        | nil =>
          have produced := inferExprFuel_declaration_normalized_formation formation.toFormationContext
            formation.scope.binders expressionEq allocationEq lookupNone notBoolean functionsResult
            expectedFormed continuation original
          exact ⟨produced.1, expression_state_from_rows formed original produced.2⟩
        | cons second tail => simp at success
  case case25 =>
    intros fuel context initial
    unfold InferConstructorArgumentsFuelFormation
    intro ready nodes formed formation below expected result success continuation captures
    simp only [inferConstructorArgumentsFuel, pure, Pure.pure, Except.pure, Except.ok.injEq] at success
    subst result
    exact ⟨by simp, formed⟩
  case case29 =>
    intros context expectedReturn initial fuel
    unfold InferStatementsFuelFormation
    intro ready nodes formed formation below expected result success continuation captures
    simp only [inferStatementsFuel, Except.ok.injEq] at success
    subst result
    exact ⟨.unit formation.scope.binders, formed⟩
  case case53 =>
    intros fuel context initial
    unfold InferForItemsFuelFormation
    intro ready nodes formed formation  result success continuation captures items
    simp only [inferForItemsFuel, pure, Pure.pure, Except.pure, Except.ok.injEq] at success
    subst result
    exact formed
  case case72 =>
    intros context initial fuel
    unfold InferExprsFuelFormation
    intro ready nodes formed formation  result success continuation captures
    simp only [inferExprsFuel, Except.ok.injEq] at success
    subst result
    exact ⟨by simp, formed⟩
  case case75 =>
    intros context scrutineeType expectedReturn outerScope initial fuel
    unfold InferMatchCasesFuelFormation
    intro ready nodes formed formation scrutineeBelow scrutineeFormed returnBelow returnFormed scopeEq result success continuation captures
    simp only [inferMatchCasesFuel, Except.ok.injEq] at success
    subst result
    exact formed
  case case23 =>
    intros fuel context source id instantiation arguments expected initial arityEq argumentsInduction
    exact inferConstructorApplicationFuel_formation argumentsInduction
  case case26 =>
    intros fuel context source sources expected expectedTypes initial sourceIH tailIH
    exact inferConstructorArgumentsFuel_cons_formation sourceIH tailIH
  case case58 =>
    intros context item initial fuel name initializer itemEq initializerInduction
    unfold InferForItemFuelFormation
    intro ready nodes formed formation result success continuation captures headerCaptures
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases initializerResult : inferExprFuel fuel context initializer none initial with
    | error error => simp [initializerResult] at success
    | ok pair =>
      rcases pair with ⟨inferred, initializerState⟩
      simp only [initializerResult, pure, Pure.pure, Except.pure] at success
      let receipt : LocalHeaderRequirementTiming.Receipt fuel context item initial result :=
        ⟨name, initializer, none, none, .none, itemEq, inferred, initializerState,
          initializerResult, (Except.ok.inj success).symm⟩
      exact initialized_header_receipt_normalized receipt initializerInduction
        ready nodes formed formation continuation captures headerCaptures
  case case59 =>
    intros context item initial fuel name sourceType initializer itemEq initializerInduction
    unfold InferForItemFuelFormation
    intro ready nodes formed formation result success continuation captures headerCaptures
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases resolution : resolveSourceType context sourceType with
    | error error => simp [resolution] at success
    | ok resolvedType =>
      simp only [resolution] at success
      cases initializerResult : inferExprFuel fuel context initializer (some resolvedType) initial with
      | error error => simp [initializerResult] at success
      | ok pair =>
        rcases pair with ⟨inferred, initializerState⟩
        simp only [initializerResult, pure, Pure.pure, Except.pure] at success
        let receipt : LocalHeaderRequirementTiming.Receipt fuel context item initial result :=
          ⟨name, initializer, some sourceType, some resolvedType, .some resolution,
            itemEq, inferred, initializerState, initializerResult, (Except.ok.inj success).symm⟩
        exact initialized_header_receipt_normalized receipt (initializerInduction resolvedType)
          ready nodes formed formation continuation captures headerCaptures
  case case34 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      name initializer statementEq initializerInduction
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocatedEq : allocated = initial.allocateStatementId.2 :=
      (congrArg Prod.snd allocationEq).symm
    have cutoffEq : allocated.nextRequirement = initial.nextRequirement := by
      rw [allocatedEq]
      rfl
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases initializerResult : inferExprFuel fuel context initializer none allocated with
    | error error => simp [initializerResult] at success
    | ok pair =>
      rcases pair with ⟨inferred, initializerState⟩
      simp only [initializerResult, pure, Pure.pure, Except.pure] at success
      let receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result := {
        name, initializer, annotation := none, expected := none, annotationAccepted := .none
        form := statementEq, value := inferred, ready := initializerState
        child := by simpa only [allocationEq] using initializerResult
        completed := by simpa only [LocalLetRequirementTiming.finish, allocationEq, cutoffEq, State.withLocals] using (Except.ok.inj success).symm }
      exact initialized_statement_receipt_normalized receipt
        (by simpa only [allocationEq] using initializerInduction)
        ready nodes formed formation continuation captures
  case case35 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      name sourceType initializer statementEq initializerInduction
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocatedEq : allocated = initial.allocateStatementId.2 :=
      (congrArg Prod.snd allocationEq).symm
    have cutoffEq : allocated.nextRequirement = initial.nextRequirement := by
      rw [allocatedEq]
      rfl
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases resolution : resolveSourceType context sourceType with
    | error error => simp [resolution] at success
    | ok resolvedType =>
      simp only [resolution] at success
      cases initializerResult : inferExprFuel fuel context initializer (some resolvedType) allocated with
      | error error => simp [initializerResult] at success
      | ok pair =>
        rcases pair with ⟨inferred, initializerState⟩
        simp only [initializerResult, pure, Pure.pure, Except.pure] at success
        let receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result := {
          name, initializer, annotation := some sourceType, expected := some resolvedType
          annotationAccepted := .some resolution
          form := statementEq, value := inferred, ready := initializerState
          child := by simpa only [allocationEq] using initializerResult
          completed := by simpa only [LocalLetRequirementTiming.finish, allocationEq, cutoffEq, State.withLocals] using (Except.ok.inj success).symm }
        exact initialized_statement_receipt_normalized receipt
          (by simpa only [allocationEq] using initializerInduction resolvedType)
          ready nodes formed formation continuation captures
  case case10 =>
    intros context expression expected initial fuel id allocated allocationEq
      inner expressionEq innerInduction
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have allocation := expression_allocation_normalized allocationEq ready nodes formed
    have expectedAllocated : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
      simpa only [allocation.2.2.2] using expectedBelow
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases innerResult : inferExprFuel fuel context inner expected allocated with
    | error error => simp [innerResult] at success
    | ok pair =>
      rcases pair with ⟨inferred, innerState⟩
      simp only [innerResult] at success
      have properties := inferExprFuel_inferenceProperties allocation.1
        formation.validated formation.functionShapes expectedAllocated innerResult
      have expectedAfter : ∀ type ∈ expected, type.VariablesBelow innerState.inference.next :=
        fun type member => (expectedAllocated type member).weaken properties.1.next_le
      have recording := recordExpressionWithExpected_inferenceProperties properties.2.1
        properties.2.2 expectedAfter success
      have innerContinuation := continuation.trans recording.1.substitution_extends
      have childFormation := innerInduction allocation.1 allocation.2.1 allocation.2.2.1
        formation expectedAllocated expectedFormed _ innerResult innerContinuation
        (captures.before_recordExpressionWithExpected success)
      exact recordExpressionWithExpected_normalized_state formation childFormation.2 continuation
        childFormation.1 expectedFormed success
  case case11 =>
    intros context expression expected initial fuel id allocated allocationEq
      elements expressionEq elementsInduction
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have allocation := expression_allocation_normalized allocationEq ready nodes formed
    have expectedAllocated : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
      simpa only [allocation.2.2.2] using expectedBelow
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases elementsResult : inferExprsFuel fuel context elements.elements allocated with
    | error error => simp [elementsResult] at success
    | ok pair =>
      rcases pair with ⟨inferredElements, elementsState⟩
      simp only [elementsResult] at success
      have properties := inferExprsFuel_inferenceProperties allocation.1
        formation.validated formation.functionShapes elementsResult
      have tupleBelow : (Ty.productMany (inferredElements.map (·.type))).VariablesBelow
          elementsState.inference.next := Ty.variablesBelow_productMany (by
        intro type member
        obtain ⟨element, present, rfl⟩ := List.mem_map.mp member
        exact properties.2.2 element present)
      have expectedAfter : ∀ type ∈ expected, type.VariablesBelow elementsState.inference.next :=
        fun type member => (expectedAllocated type member).weaken properties.1.next_le
      have recording := recordExpressionWithExpected_inferenceProperties properties.2.1
        tupleBelow expectedAfter success
      have childFormation := elementsInduction allocation.1 allocation.2.1 allocation.2.2.1 formation
        _ elementsResult (continuation.trans recording.1.substitution_extends)
        (captures.before_recordExpressionWithExpected success)
      have tupleFormed : TypeAdmissible semantic (outer.apply (Ty.productMany (inferredElements.map (·.type)))) := by
        apply normalized_productMany formation.scope.binders
        intro type member
        obtain ⟨element, present, rfl⟩ := List.mem_map.mp member
        exact childFormation.1 element present
      exact recordExpressionWithExpected_normalized_state formation childFormation.2 continuation
        tupleFormed expectedFormed success

  case case73 =>
    intros context initial fuel expression rest expressionIH tailIH
    unfold InferExprsFuelFormation
    intro ready nodes formed formation result success continuation captures
    unfold inferExprsFuel at success
    cases expressionRun : inferExprFuel fuel context expression none initial with
    | error error => simp [expressionRun, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨inferred, expressionState⟩
      simp only [expressionRun, bind, Except.bind] at success
      cases tailRun : inferExprsFuel fuel context rest expressionState with
      | error error => simp [tailRun] at success
      | ok pair =>
        rcases pair with ⟨tail, finalState⟩
        simp only [tailRun] at success
        cases success
        have expressionProperties := inferExprFuel_inferenceProperties ready
          formation.validated formation.functionShapes (by simp) expressionRun
        have expressionNodes := (inferExprFuel_occurrenceBoundExtends expressionRun).nodesBelowNextOccurrence nodes
        have tailProperties := inferExprsFuel_inferenceProperties expressionProperties.2.1
          formation.validated formation.functionShapes tailRun
        have expressionCaptures : NoCaptureNodes outer expressionState.nodes :=
          captures.of_prefix (inferExprsFuel_preserves_nodesPrefix (result := (tail, finalState)) tailRun
            (List.prefix_refl _) expressionNodes (Nat.le_refl _))
        have expressionFormation := expressionIH ready nodes formed formation
          (by simp) (by simp) _ expressionRun
          (continuation.trans tailProperties.1.substitution_extends) expressionCaptures
        have tailFormation := tailIH expressionState expressionProperties.2.1
          expressionNodes expressionFormation.2 formation _ tailRun continuation captures
        refine ⟨?_, tailFormation.2⟩
        intro element member
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact expressionFormation.1
        · exact tailFormation.1 element tailMember
  case case30 =>
    intros context expectedReturn initial fuel statement rest statementIH tailIH
    unfold InferStatementsFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    unfold inferStatementsFuel at success
    cases headRun : inferStatementFuel fuel context statement expectedReturn initial with
    | error error => simp [headRun, bind, Except.bind] at success
    | ok head =>
      simp only [headRun, bind, Except.bind] at success
      have headProperties := inferStatementFuel_inferenceProperties ready
        formation.validated formation.functionShapes returnBelow headRun
      have headNodes := (inferStatementFuel_occurrenceBoundExtends headRun).nodesBelowNextOccurrence nodes
      cases rest with
      | nil =>
        injection success with resultEq
        subst result
        have headFormation := statementIH ready nodes formed formation returnBelow returnFormed
          head headRun continuation captures
        refine ⟨?_, headFormation.2⟩
        split
        · exact headFormation.1
        · exact .unit formation.scope.binders
      | cons next remaining =>
        cases tailRun : inferStatementsFuel fuel context (next :: remaining) expectedReturn head.state with
        | error error => simp [tailRun] at success
        | ok tail =>
          simp only [tailRun] at success
          injection success with resultEq
          subst result
          have tailProperties := inferStatementsFuel_inferenceProperties headProperties.2.1
            formation.validated formation.functionShapes
            (returnBelow.weaken headProperties.1.next_le) tailRun
          have headCaptures : NoCaptureNodes outer head.state.nodes :=
            captures.of_prefix (inferStatementsFuel_preserves_nodesPrefix (result := tail) tailRun
              (List.prefix_refl _) headNodes (Nat.le_refl _))
          have headFormation := statementIH ready nodes formed formation returnBelow returnFormed
            head headRun (continuation.trans tailProperties.1.substitution_extends) headCaptures
          have tailFormation := tailIH head headProperties.2.1 headNodes headFormation.2
            formation (returnBelow.weaken headProperties.1.next_le) returnFormed
            tail tailRun continuation captures
          refine ⟨?_, tailFormation.2⟩
          split
          · exact tailFormation.1
          · split
            · exact headFormation.1
            · exact tailFormation.1

  case case60 =>
    intros context item initial fuel expression itemEq expressionIH
    unfold InferForItemFuelFormation
    intro ready nodes formed formation result success continuation captures headerCaptures
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases expressionRun : inferExprFuel fuel context expression none initial with
    | error error => simp [expressionRun] at success
    | ok pair =>
      rcases pair with ⟨inferred, expressionState⟩
      simp only [expressionRun, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      exact (expressionIH ready nodes formed formation (by simp) (by simp)
        _ expressionRun continuation captures).2
  case case61 =>
    intros context item initial fuel target operator value itemEq assignmentIH
    unfold InferForItemFuelFormation
    intro ready nodes formed formation result success continuation captures headerCaptures
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases assignmentRun : inferAssignedValueFuel fuel context target operator.value value initial with
    | error error => simp [assignmentRun] at success
    | ok triple =>
      rcases triple with ⟨assignment, inferred, assignmentState⟩
      simp only [assignmentRun, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      exact (assignmentIH ready nodes formed formation _ assignmentRun continuation captures).2.2
  case case67 =>
    intros context target initial fuel inner targetEq innerIH
    unfold InferPlaceFuelFormation at *
    intro ready nodes formed formation result success continuation captures
    exact innerIH ready nodes formed formation result
      (by simpa only [inferPlaceFuel, targetEq] using success) continuation captures
  case case64 =>
    intros context target initial fuel name targetEq binder lookupEq monomorphic
    unfold InferPlaceFuelFormation
    intro ready nodes formed formation result success continuation captures
    unfold inferPlaceFuel at success
    simp only [targetEq, lookupEq, monomorphic, if_true] at success
    injection success with resultEq
    subst result
    have binderFormed := formed.binders binder (State.lookupBinder?_eq_some_facts lookupEq).1
    exact ⟨(continuation binder.scheme.body).symm ▸ binderFormed.body, formed⟩

  case case37 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      value statementEq valueIH
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    have returnAllocated : expectedReturn.VariablesBelow allocated.inference.next := by
      simpa only [allocation.2.2.2] using returnBelow
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases valueRun : inferExprFuel fuel context value (some expectedReturn) allocated with
    | error error => simp [valueRun] at success
    | ok pair =>
      rcases pair with ⟨inferred, valueState⟩
      simp only [valueRun, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      have valueFormation := valueIH allocation.1 allocation.2.1 allocation.2.2.1 formation
        (by simpa using returnAllocated) (by simpa using returnFormed)
        _ valueRun continuation captures.before_recordNode
      exact ⟨(continuation expectedReturn).symm ▸ returnFormed, valueFormation.2.recordNode _⟩
  case case38 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      expression trailingSemicolon statementEq expressionIH
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases expressionRun : inferExprFuel fuel context expression none allocated with
    | error error => simp [expressionRun] at success
    | ok pair =>
      rcases pair with ⟨inferred, expressionState⟩
      simp only [expressionRun, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      have expressionFormation := expressionIH allocation.1 allocation.2.1 allocation.2.2.1 formation
        (by simp) (by simp) _ expressionRun continuation captures.before_recordNode
      refine ⟨?_, expressionFormation.2.recordNode _⟩
      split
      · exact .unit formation.scope.binders
      · exact expressionFormation.1
  case case41 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      target operator value statementEq assignmentIH
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases assignmentRun : inferAssignedValueFuel fuel context target operator.value value allocated with
    | error error => simp [assignmentRun] at success
    | ok triple =>
      rcases triple with ⟨assignment, inferred, assignmentState⟩
      simp only [assignmentRun, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      have assignmentFormation := assignmentIH allocation.1 allocation.2.1 allocation.2.2.1 formation
        _ assignmentRun continuation captures.before_recordNode
      exact ⟨.unit formation.scope.binders, assignmentFormation.2.2.recordNode _⟩
  case case40 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq body statementEq bodyIH
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    have returnAllocated : expectedReturn.VariablesBelow allocated.inference.next := by
      simpa only [allocation.2.2.2] using returnBelow
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases bodyRun : inferStatementsFuel fuel context body expectedReturn allocated with
    | error error => simp [bodyRun] at success
    | ok bodyResult =>
      simp only [bodyRun, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      have bodyFormation := bodyIH allocation.1 allocation.2.1 allocation.2.2.1 formation
        returnAllocated returnFormed _ bodyRun continuation captures.before_recordNode
      exact ⟨bodyFormation.1,
        (allocation.2.2.1.restore bodyFormation.2 allocated.lexicalScope (fun _ member => member)).recordNode _⟩
  case case36 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq statementEq
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases unified : Detail.unify allocated .unit expectedReturn with
    | error error => simp [unified] at success
    | ok unifiedState =>
      simp only [unified, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      exact ⟨(continuation expectedReturn).symm ▸ returnFormed,
        (allocation.2.2.1.unify unified).recordNode _⟩

  case case49 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq statementEq loopNonzero
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, loopNonzero, if_false] at success
    injection success with resultEq
    subst result
    exact ⟨.unit formation.scope.binders, allocation.2.2.1.recordNode _⟩
  case case51 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq statementEq loopNonzero
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, loopNonzero, if_false] at success
    injection success with resultEq
    subst result
    exact ⟨.unit formation.scope.binders, allocation.2.2.1.recordNode _⟩
  case case33 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq name sourceType statementEq
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases resolution : resolveSourceType context sourceType with
    | error error => simp [resolution] at success
    | ok type =>
      simp only [resolution, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      exact ⟨.unit formation.scope.binders,
        (uninitialized_binding_normalized name formation allocation.2.2.1 resolution continuation).recordNode _⟩
  case case57 =>
    intros context item initial fuel name sourceType itemEq
    unfold InferForItemFuelFormation
    intro ready nodes formed formation result success continuation captures headerCaptures
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases resolution : resolveSourceType context sourceType with
    | error error => simp [resolution] at success
    | ok type =>
      simp only [resolution, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      exact uninitialized_binding_normalized name formation formed resolution continuation
  case case54 =>
    intros fuel context item items initial itemIH tailIH
    unfold InferForItemsFuelFormation
    intro ready nodes formed formation result success continuation captures headerCaptures
    unfold inferForItemsFuel at success
    cases itemRun : inferForItemFuel fuel context item initial with
    | error error => simp [itemRun, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨inferred, itemState⟩
      simp only [itemRun, bind, Except.bind] at success
      cases tailRun : inferForItemsFuel fuel context items itemState with
      | error error => simp [tailRun] at success
      | ok tail =>
        simp only [tailRun] at success
        cases success
        have itemProperties := inferForItemFuel_inferenceProperties ready
          formation.validated formation.functionShapes itemRun
        have itemNodes := (inferForItemFuel_occurrenceBoundExtends itemRun).nodesBelowNextOccurrence nodes
        have tailProperties := inferForItemsFuel_inferenceProperties itemProperties.2
          formation.validated formation.functionShapes tailRun
        have itemCaptures : NoCaptureNodes outer itemState.nodes :=
          captures.of_prefix (inferForItemsFuel_preserves_nodesPrefix (result := tail) tailRun
            (List.prefix_refl _) itemNodes (Nat.le_refl _))
        have oneCapture : NoCaptureItems outer [inferred] := by
          intro binder member
          apply headerCaptures binder
          simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using
            (List.mem_append_left (tail.items.flatMap ForItemForm.initializedLetBinders) member)
        have restCapture : NoCaptureItems outer tail.items := by
          intro binder member
          exact headerCaptures binder (List.mem_append_right _ member)
        have itemFormation := itemIH ready nodes formed formation _ itemRun
          (continuation.trans tailProperties.1.substitution_extends) itemCaptures oneCapture
        exact tailIH itemState itemProperties.2 itemNodes itemFormation formation
          tail tailRun continuation captures restCapture

  case case18 =>
    intros context expression expected initial fuel id allocated allocationEq marker sourceType expressionEq
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have allocation := expression_allocation_normalized allocationEq ready nodes formed
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases resolution : resolveSourceType context sourceType with
    | error error => simp [resolution] at success
    | ok inner =>
      simp only [resolution] at success
      have innerFormed : TypeAdmissible semantic (outer.apply inner) :=
        (annotation_normalized_formation formation (.some resolution) 0).2 _ (by simp)
      have proxyFormed : TypeAdmissible semantic (outer.apply (.proxy inner)) :=
        .proxy innerFormed
      exact recordExpressionWithExpected_normalized_state formation allocation.2.2.1
        continuation proxyFormed expectedFormed success

  case case15 =>
    intros context expression expected initial fuel id allocated allocationEq
      keyword parameters returnType body expressionEq bodyIH
    exact inferExprFuel_lambda_formation expressionEq bodyIH

  case case62 =>
    intros context item initial fuel target operator itemEq placeIH
    unfold InferForItemFuelFormation
    intro ready nodes formed formation result success continuation captures headerCaptures
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases placeRun : inferPlaceFuel fuel context target initial with
    | error error => simp [placeRun] at success
    | ok pair =>
      rcases pair with ⟨place, placeState⟩
      simp only [placeRun] at success
      cases unified : Detail.unify placeState place.type .word with
      | error error => simp [unified] at success
      | ok unifiedState =>
        simp only [unified, pure, Pure.pure, Except.pure] at success
        injection success with resultEq
        subst result
        have placeProperties := inferPlaceFuel_inferenceProperties ready
          formation.validated formation.functionShapes placeRun
        have progress := unify_inferenceProgress placeProperties.2.1.solved
          placeProperties.2.2 (Ty.variablesBelow_constructor _ _) unified
        have placeFormation := placeIH ready nodes formed formation _ placeRun
          (continuation.trans progress.substitution_extends) (captures.before_unify unified)
        exact placeFormation.2.unify unified
  case case42 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      target operator statementEq placeIH
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases placeRun : inferPlaceFuel fuel context target allocated with
    | error error => simp [placeRun] at success
    | ok pair =>
      rcases pair with ⟨place, placeState⟩
      simp only [placeRun] at success
      cases unified : Detail.unify placeState place.type .word with
      | error error => simp [unified] at success
      | ok unifiedState =>
        simp only [unified, pure, Pure.pure, Except.pure] at success
        injection success with resultEq
        subst result
        have placeProperties := inferPlaceFuel_inferenceProperties allocation.1
          formation.validated formation.functionShapes placeRun
        have progress := unify_inferenceProgress placeProperties.2.1.solved
          placeProperties.2.2 (Ty.variablesBelow_constructor _ _) unified
        have placeFormation := placeIH allocation.1 allocation.2.1 allocation.2.2.1 formation _ placeRun
          (continuation.trans progress.substitution_extends)
          (captures.before_recordNode.before_unify unified)
        exact ⟨.unit formation.scope.binders, (placeFormation.2.unify unified).recordNode _⟩
  case case46 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      condition body statementEq conditionIH bodyIH
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    let loopContext := {context with loopDepth := context.loopDepth + 1}
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases conditionRun : inferExprFuel fuel context condition (some .bool) allocated with
    | error error => simp [conditionRun] at success
    | ok pair =>
      rcases pair with ⟨inferredCondition, conditionState⟩
      simp only [conditionRun] at success
      have conditionProperties := inferExprFuel_inferenceProperties allocation.1
        formation.validated formation.functionShapes (by
          intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _) conditionRun
      have conditionNodes := (inferExprFuel_occurrenceBoundExtends conditionRun).nodesBelowNextOccurrence allocation.2.1
      have returnCondition : expectedReturn.VariablesBelow conditionState.inference.next := by
        apply Ty.VariablesBelow.weaken _ conditionProperties.1.next_le
        simpa only [allocation.2.2.2] using returnBelow
      cases bodyRun : inferStatementsFuel fuel loopContext body.value expectedReturn conditionState with
      | error error => simp [loopContext, bodyRun] at success
      | ok bodyResult =>
        simp only [loopContext, bodyRun] at success
        injection success with resultEq
        subst result
        have bodyProperties := inferStatementsFuel_inferenceProperties (context := loopContext) conditionProperties.2.1
          formation.validated formation.functionShapes returnCondition bodyRun
        have bodyCapture : NoCaptureNodes outer bodyResult.state.nodes := captures.before_recordNode
        have conditionCapture : NoCaptureNodes outer conditionState.nodes :=
          bodyCapture.of_prefix (inferStatementsFuel_preserves_nodesPrefix (result := bodyResult) bodyRun
            (List.prefix_refl _) conditionNodes (Nat.le_refl _))
        have conditionFormation := conditionIH allocation.1 allocation.2.1 allocation.2.2.1 formation
          (by intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _)
          (by intro type member; cases Option.mem_def.mp member; exact .bool formation.scope.binders)
          _ conditionRun (continuation.trans bodyProperties.1.substitution_extends) conditionCapture
        have bodyFormation := bodyIH conditionState conditionProperties.2.1 conditionNodes conditionFormation.2
          (formation.withLoopDepth _) returnCondition returnFormed _ bodyRun continuation bodyCapture
        exact ⟨.unit formation.scope.binders,
          (conditionFormation.2.restore bodyFormation.2 conditionState.lexicalScope (fun _ member => member)).recordNode _⟩

  case case70 =>
    intros fuel context target operator value initial placeIH valueIH
    unfold InferAssignedValueFuelFormation
    intro ready nodes formed formation result success continuation captures
    unfold inferAssignedValueFuel at success
    cases placeRun : inferPlaceFuel fuel context target initial with
    | error error => simp [placeRun, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨place, placeState⟩
      simp only [placeRun, bind, Except.bind] at success
      have placeProperties := inferPlaceFuel_inferenceProperties ready
        formation.validated formation.functionShapes placeRun
      have placeNodes := (inferPlaceFuel_occurrenceBoundExtends placeRun).nodesBelowNextOccurrence nodes
      have finishValue (fitted : State)
          (progress : placeState.InferenceProgress fitted)
          (fitReady : fitted.InferenceReady) (fitNodes : fitted.NodesBelowNextOccurrence)
          (sameNodes : fitted.nodes = placeState.nodes)
          (sameBinders : fitted.localBinders = placeState.localBinders)
          (sameRows : fitted.requirements = placeState.requirements)
          (expected : Ty) (expectedBelow : expected.VariablesBelow fitted.inference.next)
          (expectedFormed : outer.SemanticallyExtends fitted.inference.substitution →
            TypeAdmissible semantic (outer.apply place.type) →
            TypeAdmissible semantic (outer.apply expected))
          (child : InferExprFuelFormation semantic outer fuel context value (some expected) fitted)
          (accepted : (do
            let (inferred, finalState) ← inferExprFuel fuel context value (some expected) fitted
            pure (({target := {place with type := finalState.resolve place.type}} : AssignmentResolution), inferred, finalState)) = .ok result) :
          TypeAdmissible semantic (outer.apply result.1.target.type) ∧
            TypeAdmissible semantic (outer.apply result.2.1.type) ∧
            NormalizedStateFormation semantic outer result.2.2 := by
        cases valueRun : inferExprFuel fuel context value (some expected) fitted with
        | error error => simp [valueRun, bind, Except.bind] at accepted
        | ok pair =>
          rcases pair with ⟨inferred, finalState⟩
          simp only [valueRun, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
          cases accepted
          have valueProperties := inferExprFuel_inferenceProperties fitReady
            formation.validated formation.functionShapes (by simpa using expectedBelow) valueRun
          have fitContinuation := continuation.trans valueProperties.1.substitution_extends
          have fitCapture : NoCaptureNodes outer fitted.nodes :=
            captures.of_prefix (inferExprFuel_preserves_nodesPrefix (result := (inferred, finalState)) valueRun
              (List.prefix_refl _) fitNodes (Nat.le_refl _))
          have placeCapture : NoCaptureNodes outer placeState.nodes := sameNodes ▸ fitCapture
          have placeFormation := placeIH ready nodes formed formation _ placeRun
            (fitContinuation.trans progress.substitution_extends) placeCapture
          have valueFormation := child fitReady fitNodes
            (placeFormation.2.congr sameBinders sameRows) formation
            (by simpa using expectedBelow) (by simpa using expectedFormed fitContinuation placeFormation.1)
            _ valueRun continuation captures
          exact ⟨(continuation place.type).symm ▸ placeFormation.1, valueFormation⟩
      have finishNonEqual
          (child : ∀ fitted, InferExprFuelFormation semantic outer fuel context value (some .word) fitted)
          (accepted : (do
            let fitted ← Detail.unify placeState place.type .word
            let (inferred, finalState) ← inferExprFuel fuel context value (some .word) fitted
            pure (({target := {place with type := finalState.resolve place.type}} : AssignmentResolution), inferred, finalState)) = .ok result) :
          TypeAdmissible semantic (outer.apply result.1.target.type) ∧
            TypeAdmissible semantic (outer.apply result.2.1.type) ∧
            NormalizedStateFormation semantic outer result.2.2 := by
        cases fitRun : Detail.unify placeState place.type .word with
        | error error => simp [fitRun, bind, Except.bind] at accepted
        | ok fitted =>
          simp only [fitRun, bind, Except.bind] at accepted
          have progress := unify_inferenceProgress placeProperties.2.1.solved
            placeProperties.2.2 (Ty.variablesBelow_constructor _ _) fitRun
          have fitReady := unify_preserves_inferenceReady placeProperties.2.1
            placeProperties.2.2 (Ty.variablesBelow_constructor _ _) fitRun
          have fitNodes : fitted.NodesBelowNextOccurrence := by
            intro node member
            rw [(unify_occurrenceState_eq fitRun).1] at member
            rw [(unify_occurrenceState_eq fitRun).2]
            exact placeNodes node member
          exact finishValue fitted progress fitReady fitNodes (unify_occurrenceState_eq fitRun).1
            (congrArg LexicalScope.binders (unify_preserves_lexicalScope fitRun)) (unify_requirements_eq fitRun)
            .word (Ty.variablesBelow_constructor _ _) (fun _ _ => .word formation.scope.binders)
            (child fitted) accepted
      cases operator with
      | equal =>
        simp only [pure, Pure.pure, Except.pure] at success
        exact finishValue placeState (.refl placeProperties.2.1.solved) placeProperties.2.1
          placeNodes rfl rfl rfl (placeState.resolve place.type)
          (placeProperties.2.1.solved.variablesBelow_apply placeProperties.2.2)
          (fun extension formedType => (extension place.type).symm ▸ formedType)
          (valueIH place placeState) success
      | add => exact finishNonEqual (valueIH place) success
      | subtract => exact finishNonEqual (valueIH place) success
      | multiply => exact finishNonEqual (valueIH place) success
      | divide => exact finishNonEqual (valueIH place) success
      | modulo => exact finishNonEqual (valueIH place) success
      | bitAnd => exact finishNonEqual (valueIH place) success
      | bitXor => exact finishNonEqual (valueIH place) success
      | bitOr => exact finishNonEqual (valueIH place) success

  case case14 =>
    intros context expression expected initial fuel id allocated allocationEq
      condition question thenBranch colon elseBranch expressionEq conditionIH thenIH elseIH
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have allocation := expression_allocation_normalized allocationEq ready nodes formed
    have expectedAllocated : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
      simpa only [allocation.2.2.2] using expectedBelow
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases conditionRun : inferExprFuel fuel context condition (some .bool) allocated with
    | error error => simp [conditionRun] at success
    | ok pair =>
      rcases pair with ⟨conditionValue, conditionState⟩
      simp only [conditionRun] at success
      have conditionProperties := inferExprFuel_inferenceProperties allocation.1
        formation.validated formation.functionShapes (by
          intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _) conditionRun
      have conditionNodes := (inferExprFuel_occurrenceBoundExtends conditionRun).nodesBelowNextOccurrence allocation.2.1
      have expectedCondition : ∀ type ∈ expected, type.VariablesBelow conditionState.inference.next :=
        fun type member => (expectedAllocated type member).weaken conditionProperties.1.next_le
      cases thenRun : inferExprFuel fuel context thenBranch expected conditionState with
      | error error => simp [thenRun] at success
      | ok pair =>
        rcases pair with ⟨thenValue, thenState⟩
        simp only [thenRun] at success
        have thenProperties := inferExprFuel_inferenceProperties conditionProperties.2.1
          formation.validated formation.functionShapes expectedCondition thenRun
        have thenNodes := (inferExprFuel_occurrenceBoundExtends thenRun).nodesBelowNextOccurrence conditionNodes
        have expectedThen : ∀ type ∈ expected, type.VariablesBelow thenState.inference.next :=
          fun type member => (expectedCondition type member).weaken thenProperties.1.next_le
        cases elseRun : inferExprFuel fuel context elseBranch expected thenState with
        | error error => simp [elseRun] at success
        | ok pair =>
          rcases pair with ⟨elseValue, elseState⟩
          simp only [elseRun] at success
          have elseProperties := inferExprFuel_inferenceProperties thenProperties.2.1
            formation.validated formation.functionShapes expectedThen elseRun
          have thenBelow := thenProperties.2.2.weaken elseProperties.1.next_le
          cases unified : Detail.unify elseState thenValue.type elseValue.type with
          | error error => simp [unified] at success
          | ok unifiedState =>
            simp only [unified] at success
            have unifyProgress := unify_inferenceProgress elseProperties.2.1.solved
              thenBelow elseProperties.2.2 unified
            have unifiedReady := unify_preserves_inferenceReady elseProperties.2.1
              thenBelow elseProperties.2.2 unified
            have expectedUnified : ∀ type ∈ expected, type.VariablesBelow unifiedState.inference.next :=
              fun type member => (expectedThen type member).weaken
                (elseProperties.1.trans unifyProgress).next_le
            have recording := recordExpressionWithExpected_inferenceProperties unifiedReady
              (unifyProgress.resolve_variablesBelow thenBelow) expectedUnified success
            have unifiedContinuation := continuation.trans recording.1.substitution_extends
            have elseContinuation := unifiedContinuation.trans unifyProgress.substitution_extends
            have thenContinuation := elseContinuation.trans elseProperties.1.substitution_extends
            have conditionContinuation := thenContinuation.trans thenProperties.1.substitution_extends
            have unifiedCapture : NoCaptureNodes outer unifiedState.nodes :=
              captures.before_recordExpressionWithExpected success
            have elseCapture := unifiedCapture.before_unify unified
            have thenCapture : NoCaptureNodes outer thenState.nodes :=
              elseCapture.of_prefix (inferExprFuel_preserves_nodesPrefix
                (result := (elseValue, elseState)) elseRun (List.prefix_refl _) thenNodes (Nat.le_refl _))
            have conditionCapture : NoCaptureNodes outer conditionState.nodes :=
              thenCapture.of_prefix (inferExprFuel_preserves_nodesPrefix
                (result := (thenValue, thenState)) thenRun (List.prefix_refl _) conditionNodes (Nat.le_refl _))
            have conditionFormation := conditionIH allocation.1 allocation.2.1 allocation.2.2.1 formation
              (by intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _)
              (by intro type member; cases Option.mem_def.mp member; exact .bool formation.scope.binders)
              _ conditionRun conditionContinuation conditionCapture
            have thenFormation := thenIH conditionState conditionProperties.2.1 conditionNodes
              conditionFormation.2 formation expectedCondition expectedFormed _ thenRun thenContinuation thenCapture
            have elseFormation := elseIH thenState thenProperties.2.1 thenNodes thenFormation.2 formation
              expectedThen expectedFormed _ elseRun elseContinuation elseCapture
            exact recordExpressionWithExpected_normalized_state formation (elseFormation.2.unify unified)
              continuation ((unifiedContinuation thenValue.type).symm ▸ thenFormation.1) expectedFormed success

  case case43 =>
    intro context statement expectedReturn initial fuel id allocated allocationEq scrutinees arms form
    dsimp only
    intro source single casesIH bodyIH sourceIH
    apply inferStatementFuel_match_single_formation form single casesIH bodyIH
    simpa only [allocationEq] using sourceIH
  case case44 =>
    intro context statement expectedReturn initial fuel id allocated allocationEq scrutinees arms form
    dsimp only
    intro notSingleton casesIH bodyIH sourcesIH
    apply inferStatementFuel_match_many_formation form notSingleton casesIH bodyIH
    simpa only [allocationEq] using sourcesIH
  case case76 =>
    intros context scrutineeType expectedReturn outerScope initial fuel arm rest bodyIH tailIH
    exact inferMatchCasesFuel_cons_formation bodyIH tailIH

  case case39 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      condition thenBody elseBody statementEq conditionIH thenIH elseIH
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    have returnAllocated : expectedReturn.VariablesBelow allocated.inference.next := by
      simpa only [allocation.2.2.2] using returnBelow
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases conditionRun : inferExprFuel fuel context condition (some .bool) allocated with
    | error error => simp [conditionRun] at success
    | ok pair =>
      rcases pair with ⟨conditionValue, conditionState⟩
      simp only [conditionRun] at success
      have conditionProperties := inferExprFuel_inferenceProperties allocation.1
        formation.validated formation.functionShapes (by
          intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _) conditionRun
      have conditionNodes := (inferExprFuel_occurrenceBoundExtends conditionRun).nodesBelowNextOccurrence allocation.2.1
      have returnCondition := returnAllocated.weaken conditionProperties.1.next_le
      cases thenRun : inferStatementsFuel fuel context thenBody.value expectedReturn conditionState with
      | error error => simp [thenRun] at success
      | ok thenResult =>
        simp only [thenRun] at success
        have thenProperties := inferStatementsFuel_inferenceProperties conditionProperties.2.1
          formation.validated formation.functionShapes returnCondition thenRun
        have thenNodes := (inferStatementsFuel_occurrenceBoundExtends thenRun).nodesBelowNextOccurrence conditionNodes
        let afterThen := thenResult.state.restoreLexicalScope conditionState.lexicalScope
        have restored : conditionState.InferenceProgress afterThen ∧ afterThen.InferenceReady :=
          State.restoreLexicalScope_inferenceProperties conditionProperties.2.1 thenProperties.1
        have prefixFormation
            (thenContinuation : outer.SemanticallyExtends thenResult.state.inference.substitution)
            (thenCapture : NoCaptureNodes outer thenResult.state.nodes) :
            NormalizedStateFormation semantic outer conditionState ∧
              NormalizedStateFormation semantic outer afterThen := by
          have conditionCapture : NoCaptureNodes outer conditionState.nodes :=
            thenCapture.of_prefix (inferStatementsFuel_preserves_nodesPrefix (result := thenResult) thenRun
              (List.prefix_refl _) conditionNodes (Nat.le_refl _))
          have conditionFormation := conditionIH allocation.1 allocation.2.1 allocation.2.2.1 formation
            (by intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _)
            (by intro type member; cases Option.mem_def.mp member; exact .bool formation.scope.binders)
            _ conditionRun (thenContinuation.trans thenProperties.1.substitution_extends) conditionCapture
          have thenFormation := thenIH conditionState conditionProperties.2.1 conditionNodes conditionFormation.2
            formation returnCondition returnFormed _ thenRun thenContinuation thenCapture
          exact ⟨conditionFormation.2,
            conditionFormation.2.restore thenFormation.2 conditionState.lexicalScope (fun _ member => member)⟩
        cases elseBody with
        | none =>
          simp only [pure, Pure.pure, Except.pure] at success
          injection success with resultEq
          subst result
          have prior := prefixFormation continuation captures.before_recordNode
          exact ⟨.unit formation.scope.binders, prior.2.recordNode _⟩
        | some elseBody =>
          cases elseRun : inferStatementsFuel fuel context elseBody.value expectedReturn afterThen with
          | error error => simp [afterThen, elseRun] at success
          | ok elseResult =>
            simp only [afterThen, elseRun, pure, Pure.pure, Except.pure] at success
            injection success with resultEq
            subst result
            have elseProperties := inferStatementsFuel_inferenceProperties restored.2
              formation.validated formation.functionShapes (returnCondition.weaken restored.1.next_le) elseRun
            have elseCapture : NoCaptureNodes outer elseResult.state.nodes := captures.before_recordNode
            have thenCapture : NoCaptureNodes outer thenResult.state.nodes :=
              elseCapture.of_prefix (inferStatementsFuel_preserves_nodesPrefix (result := elseResult) elseRun
                (List.prefix_refl _) thenNodes (Nat.le_refl _))
            have prior := prefixFormation (continuation.trans elseProperties.1.substitution_extends) thenCapture
            have elseFormation := elseIH conditionState thenResult elseBody restored.2 thenNodes prior.2
              formation (returnCondition.weaken restored.1.next_le) returnFormed _ elseRun continuation elseCapture
            refine ⟨?_, (prior.1.restore elseFormation.2 conditionState.lexicalScope (fun _ member => member)).recordNode _⟩
            split
            · exact (continuation expectedReturn).symm ▸ returnFormed
            · exact .unit formation.scope.binders

  case case16 =>
    intro context expression expected initial fuel id allocated allocationEq callee arguments expressionEq constructorIH argumentsIH calleeIH
    apply inferExprFuel_call_formation expressionEq
    · intro instantiation state
      simpa only [allocationEq] using constructorIH instantiation state
    · simpa only [allocationEq] using argumentsIH
    · exact calleeIH
  case case17 =>
    intro context expression expected initial fuel id allocated allocationEq dot name arguments expressionEq constructorIH
    apply inferExprFuel_dotConstructor_formation expressionEq
    intro dataType constructor typeArguments
    simpa only [allocationEq] using constructorIH dataType constructor typeArguments
  case case20 =>
    intro context expression expected initial fuel id allocated allocationEq base dot name expressionEq constructorIH
    apply inferExprFuel_fieldConstructor_formation expressionEq
    intro instantiation state
    simpa only [allocationEq] using constructorIH instantiation state

  case case12 =>
    intro context expression expected initial fuel id allocated allocationEq operator operand form operandIH
    apply inferExprFuel_unary_formation form
    simpa only [allocationEq] using operandIH
  case case13 =>
    intro context expression expected initial fuel id allocated allocationEq left operator right form leftIH rightIH
    apply inferExprFuel_binary_formation form
    · simpa only [allocationEq] using leftIH
    · exact rightIH
  case case19 =>
    intro context expression expected initial fuel id allocated allocationEq base brackets index form baseIH indexIH
    apply inferExprFuel_index_formation form
    · simpa only [allocationEq] using baseIH
    · exact indexIH
  case case68 =>
    intro context target initial fuel base brackets key form baseIH keyIH
    exact inferPlaceFuel_index_formation form baseIH keyIH
  case case45 =>
    intro context statement expectedReturn initial fuel id allocated allocationEq headerSpan initializer condition post body form initializerIH conditionIH bodyIH postIH
    apply inferStatementFuel_for_formation form
    · simpa only [allocationEq] using initializerIH
    · exact conditionIH
    · exact bodyIH
    · exact postIH

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferExprFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context expression expected state,
      InferExprFuelFormation semantic outer fuel context expression expected state :=
  (inferFuel_formation_internal semantic outer).1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferConstructorApplicationFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context source id instantiation arguments expected state,
      InferConstructorApplicationFuelFormation semantic outer fuel context source id instantiation arguments expected state :=
  (inferFuel_formation_internal semantic outer).2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferConstructorArgumentsFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context sources expected state,
      InferConstructorArgumentsFuelFormation semantic outer fuel context sources expected state :=
  (inferFuel_formation_internal semantic outer).2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferStatementsFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context statements expectedReturn state,
      InferStatementsFuelFormation semantic outer fuel context statements expectedReturn state :=
  (inferFuel_formation_internal semantic outer).2.2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferStatementFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context statement expectedReturn state,
      InferStatementFuelFormation semantic outer fuel context statement expectedReturn state :=
  (inferFuel_formation_internal semantic outer).2.2.2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferForItemsFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context items state,
      InferForItemsFuelFormation semantic outer fuel context items state :=
  (inferFuel_formation_internal semantic outer).2.2.2.2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferForItemFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context item state,
      InferForItemFuelFormation semantic outer fuel context item state :=
  (inferFuel_formation_internal semantic outer).2.2.2.2.2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferPlaceFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context target state,
      InferPlaceFuelFormation semantic outer fuel context target state :=
  (inferFuel_formation_internal semantic outer).2.2.2.2.2.2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferAssignedValueFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context target operator value state,
      InferAssignedValueFuelFormation semantic outer fuel context target operator value state :=
  (inferFuel_formation_internal semantic outer).2.2.2.2.2.2.2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferExprsFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context expressions state,
      InferExprsFuelFormation semantic outer fuel context expressions state :=
  (inferFuel_formation_internal semantic outer).2.2.2.2.2.2.2.2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferMatchCasesFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context scrutineeType expectedReturn outerScope cases state,
      InferMatchCasesFuelFormation semantic outer fuel context scrutineeType expectedReturn outerScope cases state :=
  (inferFuel_formation_internal semantic outer).2.2.2.2.2.2.2.2.2.2


end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
