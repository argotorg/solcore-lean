import Solcore.SourceSemantics.Internal.Inference.Ledgers
import Solcore.SourceSemantics.Internal.Inference.StatementControl

/-!
# Ledger families

The same ledgers through places, `for` headers and the statement family. See
`Internal/Inference/ExpressionLedgers` for why this file stays apart from it.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceForItemsLedgerInvariant
/-!
Pending qualified-template IDs accumulate in source order through a `for`
initializer or post list.  The enclosing loop statement will materialize the
entire pending inventory after both traversals complete.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Unlike an ordinary let statement, a `for` header does not record its
own node.  Newly generalized templates therefore remain pending, exactly as
the emitted item form reports. -/
theorem generalizedInitializedForItem_ledger
    {state binderState : State} {pending : List RequirementId}
    {locals : TypeSystem.Environment} {requirementStart : Nat}
    {type : Ty} {name : Syntax.Identifier}
    {generalized : Detail.GeneralizedValue} {binder : TypedBinder}
    {initializer : ExpressionId}
    (tracked : RecursiveLedgerInvariant state pending)
    (generalizedEq : generalized = Detail.generalizeValue state locals
      requirementStart type)
    (bindingEq : (state.withLocals locals).allocateBinder name.value
      generalized.scheme (some name.span) false generalized.requirements =
        (binder, binderState)) :
    RecursiveLedgerInvariant binderState
      (pending ++ (ForItemForm.letDecl binder (some initializer)
        ).localSchemeTemplateIds) := by
  have allocatedTracked : RecursiveLedgerInvariant binderState
      (pending ++ generalized.requirements.map fun requirement =>
        requirement.templateRequirement) := by
    simpa [← generalizedEq, bindingEq] using
      tracked.allocateGeneralizedValue locals requirementStart type
        name.value (some name.span)
  have binderRequirementsEq : binder.schemeRequirements =
      generalized.requirements := by
    have projected := congrArg
      (fun pair : TypedBinder × State => pair.1.schemeRequirements) bindingEq
    simpa [State.allocateBinder] using projected.symm
  simpa [ForItemForm.localSchemeTemplateIds, binderRequirementsEq] using
    allocatedTracked

/-- An uninitialized header let introduces no qualified templates because
its generalization barrier begins at the current end of the ledger. -/
theorem generalizedUninitializedForItem_ledger
    {state binderState : State} {pending : List RequirementId}
    {locals : TypeSystem.Environment} {type : Ty}
    {name : Syntax.Identifier}
    {generalized : Detail.GeneralizedValue} {binder : TypedBinder}
    (tracked : RecursiveLedgerInvariant state pending)
    (generalizedEq : generalized = Detail.generalizeValue state locals
      state.nextRequirement type)
    (bindingEq : (state.withLocals locals).allocateBinder name.value
      generalized.scheme (some name.span) false generalized.requirements =
        (binder, binderState)) :
    RecursiveLedgerInvariant binderState
      (pending ++ (ForItemForm.letDecl binder none).localSchemeTemplateIds) := by
  have requirementsEmpty : generalized.requirements = [] := by
    rw [generalizedEq]
    exact generalizeValue_requirements_empty_at_next state locals type
      tracked.requirements
  have allocatedTracked : RecursiveLedgerInvariant binderState pending := by
    have trackedWithPending :=
      tracked.allocateGeneralizedValue locals state.nextRequirement type
        name.value (some name.span)
    dsimp only at trackedWithPending
    rw [← generalizedEq, bindingEq] at trackedWithPending
    simpa [requirementsEmpty] using trackedWithPending
  simpa [ForItemForm.localSchemeTemplateIds] using allocatedTracked

theorem inferForItemFuel_expression_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {expression : Syntax.Expr}
    {initial : State} {result : ForItemForm × State}
    {pending : List RequirementId}
    (itemEq : item.value = .expression expression)
    (success : Detail.inferForItemFuel (fuel + 1) context item initial =
      .ok result)
    (expressionIH : InferExprFuelLedgerPreservation fuel)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.2
      (pending ++ result.1.localSchemeTemplateIds) := by
  obtain ⟨_, childState, childSuccess, resultEq⟩ :=
    inferForItemFuel_success_expression_facts itemEq success
  rw [resultEq]
  simpa [ForItemForm.localSchemeTemplateIds] using
    expressionIH childSuccess tracked

theorem inferForItemFuel_letUnannotatedInitialized_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {name : Syntax.Identifier}
    {initializer : Syntax.Expr} {initial : State}
    {result : ForItemForm × State} {pending : List RequirementId}
    (itemEq : item.value = .letDecl name none (some initializer))
    (success : Detail.inferForItemFuel (fuel + 1) context item initial =
      .ok result)
    (expressionIH : InferExprFuelLedgerPreservation fuel)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.2
      (pending ++ result.1.localSchemeTemplateIds) := by
  obtain ⟨_, initializerState, locals, valueType, generalized, binding,
      initializerSuccess, _, _, generalizedEq, bindingEq, resultEq⟩ :=
    inferForItemFuel_success_letUnannotatedInitialized_facts itemEq success
  rcases binding with ⟨binder, binderState⟩
  rw [resultEq]
  exact generalizedInitializedForItem_ledger
    (expressionIH initializerSuccess tracked) generalizedEq bindingEq

theorem inferForItemFuel_letAnnotatedInitialized_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {initializer : Syntax.Expr}
    {initial : State} {result : ForItemForm × State}
    {pending : List RequirementId}
    (itemEq : item.value = .letDecl name (some sourceType)
      (some initializer))
    (success : Detail.inferForItemFuel (fuel + 1) context item initial =
      .ok result)
    (expressionIH : InferExprFuelLedgerPreservation fuel)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.2
      (pending ++ result.1.localSchemeTemplateIds) := by
  obtain ⟨_, _, initializerState, locals, valueType, generalized, binding,
      _, initializerSuccess, _, _, generalizedEq, bindingEq, resultEq⟩ :=
    inferForItemFuel_success_letAnnotatedInitialized_facts itemEq success
  rcases binding with ⟨binder, binderState⟩
  rw [resultEq]
  exact generalizedInitializedForItem_ledger
    (expressionIH initializerSuccess tracked) generalizedEq bindingEq

theorem inferForItemFuel_letAnnotatedUninitialized_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {initial : State}
    {result : ForItemForm × State} {pending : List RequirementId}
    (itemEq : item.value = .letDecl name (some sourceType) none)
    (success : Detail.inferForItemFuel (fuel + 1) context item initial =
      .ok result)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.2
      (pending ++ result.1.localSchemeTemplateIds) := by
  obtain ⟨_, locals, valueType, generalized, binding, _, _, _,
      generalizedEq, bindingEq, resultEq⟩ :=
    inferForItemFuel_success_letAnnotatedUninitialized_facts itemEq success
  rcases binding with ⟨binder, binderState⟩
  rw [resultEq]
  exact generalizedUninitializedForItem_ledger tracked generalizedEq bindingEq

theorem inferForItemFuel_assignValue_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {target value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp}
    {initial : State} {result : ForItemForm × State}
    {pending : List RequirementId}
    (itemEq : item.value = .assignValue target operator value)
    (success : Detail.inferForItemFuel (fuel + 1) context item initial =
      .ok result)
    (assignmentIH : InferAssignedValueFuelLedgerPreservation fuel)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.2
      (pending ++ result.1.localSchemeTemplateIds) := by
  obtain ⟨_, _, childState, childSuccess, resultEq⟩ :=
    inferForItemFuel_success_assignValue_facts itemEq success
  rw [resultEq]
  simpa [ForItemForm.localSchemeTemplateIds] using
    assignmentIH childSuccess tracked

theorem inferForItemFuel_assignBitNot_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {target : Syntax.Expr}
    {operatorSpan : Syntax.SourceSpan}
    {initial : State} {result : ForItemForm × State}
    {pending : List RequirementId}
    (itemEq : item.value = .assignBitNot target operatorSpan)
    (success : Detail.inferForItemFuel (fuel + 1) context item initial =
      .ok result)
    (placeIH : InferPlaceFuelLedgerPreservation fuel)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.2
      (pending ++ result.1.localSchemeTemplateIds) := by
  obtain ⟨place, placeState, unifiedState, placeSuccess, unifiedSuccess,
      resultEq⟩ :=
    inferForItemFuel_success_assignBitNot_facts itemEq success
  rw [resultEq]
  simpa [ForItemForm.localSchemeTemplateIds] using
    (placeIH placeSuccess tracked).unify unifiedSuccess

/-- One actual `for` item extends the pending template suffix by precisely
the qualified requirements retained in its emitted form. -/
theorem inferForItemFuelLedgerPreservation_step
    {fuel : Nat}
    (expressionIH : InferExprFuelLedgerPreservation fuel)
    (placeIH : InferPlaceFuelLedgerPreservation fuel)
    (assignmentIH : InferAssignedValueFuelLedgerPreservation fuel) :
    InferForItemFuelLedgerPreservation (fuel + 1) := by
  intro context item initial final inferred pending success tracked
  cases itemEq : item.value
  case letDecl name sourceType initializer =>
    cases sourceType with
    | none =>
        cases initializer with
        | none =>
            simp [Detail.inferForItemFuel, itemEq, bind, Except.bind]
              at success
        | some initializer =>
            exact inferForItemFuel_letUnannotatedInitialized_ledger itemEq
              success expressionIH tracked
    | some sourceType =>
        cases initializer with
        | none =>
            exact inferForItemFuel_letAnnotatedUninitialized_ledger itemEq
              success tracked
        | some initializer =>
            exact inferForItemFuel_letAnnotatedInitialized_ledger itemEq
              success expressionIH tracked
  case expression expression =>
    exact inferForItemFuel_expression_ledger itemEq success expressionIH tracked
  case assignValue target operator value =>
    exact inferForItemFuel_assignValue_ledger itemEq success assignmentIH
      tracked
  case assignBitNot target operatorSpan =>
    exact inferForItemFuel_assignBitNot_ledger itemEq success placeIH tracked

/-- Source-ordered `for` header sequencing from one actual item theorem.
The suffix is indexed by the inferred item forms, not by syntactic guesses
about which inputs generalize. -/
theorem inferForItemsFuelLedgerPreservation_of_itemSoundness
    {fuel : Nat}
    (itemSound : InferForItemFuelLedgerPreservation fuel) :
    InferForItemsFuelLedgerPreservation fuel := by
  intro context items initial result pending success tracked
  induction items generalizing initial result pending with
  | nil =>
      simp only [Detail.inferForItemsFuel, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      simpa using tracked
  | cons item rest induction =>
      unfold Detail.inferForItemsFuel at success
      cases itemSuccess : Detail.inferForItemFuel fuel context item initial with
      | error error =>
          simp [itemSuccess, bind, Except.bind] at success
      | ok itemResult =>
          rcases itemResult with ⟨inferred, itemState⟩
          simp only [itemSuccess, bind, Except.bind] at success
          cases tailSuccess : Detail.inferForItemsFuel fuel context rest
              itemState with
          | error error =>
              simp [tailSuccess] at success
          | ok tail =>
              simp only [tailSuccess, pure, Pure.pure, Except.pure] at success
              injection success with resultEq
              subst result
              have itemTracked := itemSound itemSuccess tracked
              have tailTracked := induction tailSuccess itemTracked
              simpa [List.flatMap_cons, List.append_assoc] using tailTracked

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferencePlaceLedgerInvariant
/-!
Pending-indexed requirement/template ledger preservation for assignable
places and value assignments.  Mapping keys are the only expression children
of places; their actual inference success is passed to the smaller-fuel
expression contract.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

namespace RecursiveLedgerInvariant

/-- Fresh type variables modify inference data but neither requirement rows
nor qualified-template ownership. -/
theorem fresh {state : State} {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending) :
    RecursiveLedgerInvariant state.fresh.2 pending := by
  constructor
  · exact State.fresh_preserves_requirementsWellFormed state
      tracked.requirements
  · constructor
    · change state.localSchemeAssumptions.Perm
        (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++ pending)
      exact tracked.templates.classified
    · change state.localSchemeAssumptions.Nodup
      exact tracked.templates.unique
    · change ∀ id, id ∈ state.localSchemeAssumptions →
        id ∈ state.requirements.map (fun requirement => requirement.id)
      exact tracked.templates.covered

end RecursiveLedgerInvariant

/-- Every successful place traversal preserves the ambient pending template
suffix.  Indexing first infers the base place, then freshens two types,
unifies with a mapping, and infers the one actual key expression. -/
theorem inferPlaceFuel_ledgerPreservation :
    ∀ fuel, (∀ childFuel, childFuel < fuel →
      InferExprFuelLedgerPreservation childFuel) →
      InferPlaceFuelLedgerPreservation fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro _ context target initial final place pending success
      simp [Detail.inferPlaceFuel] at success
  | succ fuel induction =>
      intro expressionLedger context target initial final place pending
        success tracked
      cases targetEq : target.value with
      | identifier name =>
          unfold Detail.inferPlaceFuel at success
          simp only [targetEq] at success
          cases lookup : initial.lookupBinder? name.value with
          | none => simp [lookup] at success
          | some binder =>
              simp only [lookup] at success
              split at success
              · injection success with resultEq
                injection resultEq with _ finalEq
                subst final
                exact tracked
              · simp at success
      | group inner =>
          have innerSuccess : Detail.inferPlaceFuel fuel context inner initial =
              .ok (place, final) := by
            simpa only [Detail.inferPlaceFuel, targetEq] using success
          exact induction (fun childFuel childLt => expressionLedger childFuel
            (Nat.lt_trans childLt (Nat.lt_succ_self fuel))) innerSuccess
            tracked
      | index base brackets key =>
          unfold Detail.inferPlaceFuel at success
          simp only [targetEq, bind, Except.bind] at success
          cases baseResult : Detail.inferPlaceFuel fuel context base initial with
          | error error => simp [baseResult] at success
          | ok basePair =>
              rcases basePair with ⟨basePlace, baseState⟩
              simp only [baseResult] at success
              let keyAllocation := baseState.fresh
              let valueAllocation := keyAllocation.2.fresh
              cases unifyResult : Detail.unify valueAllocation.2
                  basePlace.type (.mapping keyAllocation.1 valueAllocation.1)
                with
              | error error =>
                  simp [keyAllocation, valueAllocation, unifyResult] at success
              | ok unifiedState =>
                  simp only [keyAllocation, valueAllocation, unifyResult]
                    at success
                  cases keyResult : Detail.inferExprFuel fuel context key
                      (some (unifiedState.resolve keyAllocation.1))
                      unifiedState with
                  | error error =>
                      simp [keyAllocation, keyResult] at success
                  | ok keyPair =>
                      rcases keyPair with ⟨inferredKey, keyState⟩
                      simp only [keyAllocation, keyResult, pure, Pure.pure,
                        Except.pure] at success
                      injection success with resultEq
                      injection resultEq with _ finalEq
                      subst final
                      have baseTracked : RecursiveLedgerInvariant baseState
                          pending := induction
                            (fun childFuel childLt => expressionLedger
                              childFuel (Nat.lt_trans childLt
                                (Nat.lt_succ_self fuel))) baseResult tracked
                      have keyAllocated : RecursiveLedgerInvariant
                          keyAllocation.2 pending := baseTracked.fresh
                      have valueAllocated : RecursiveLedgerInvariant
                          valueAllocation.2 pending := keyAllocated.fresh
                      have unifiedTracked : RecursiveLedgerInvariant
                          unifiedState pending :=
                        valueAllocated.unify unifyResult
                      exact expressionLedger fuel (Nat.lt_succ_self fuel)
                        keyResult unifiedTracked
      | _ =>
          simp [Detail.inferPlaceFuel, targetEq] at success

/-- Assignment first traverses the place, optionally unifies it with `Word`,
then infers the right-hand side at the resulting expected type. -/
theorem inferAssignedValueFuel_ledgerPreservation
    {fuel : Nat}
    (placeLedger : InferPlaceFuelLedgerPreservation fuel)
    (expressionLedger : InferExprFuelLedgerPreservation fuel) :
    InferAssignedValueFuelLedgerPreservation fuel := by
  intro context target value operator initial final assignment inferred pending
    success tracked
  unfold Detail.inferAssignedValueFuel at success
  cases placeResult : Detail.inferPlaceFuel fuel context target initial with
  | error error => simp [placeResult, bind, Except.bind] at success
  | ok placePair =>
      rcases placePair with ⟨place, placeState⟩
      simp only [placeResult, bind, Except.bind, Prod.eta] at success
      have placeTracked : RecursiveLedgerInvariant placeState pending :=
        placeLedger placeResult tracked
      have finishNonEqual
          (tailSuccess :
            (do
              let fittedState ← Detail.unify placeState place.type .word
              let (inferredValue, finalState) ←
                Detail.inferExprFuel fuel context value (some .word)
                  fittedState
              pure (({ target := { place with
                type := finalState.resolve place.type } } :
                  AssignmentResolution), inferredValue, finalState)) =
                .ok (assignment, inferred, final)) :
          RecursiveLedgerInvariant final pending := by
        cases unifyResult : Detail.unify placeState place.type .word with
        | error error =>
            simp [unifyResult, bind, Except.bind] at tailSuccess
        | ok fittedState =>
            simp only [unifyResult, bind, Except.bind] at tailSuccess
            cases valueResult : Detail.inferExprFuel fuel context value
                (some .word) fittedState with
            | error error => simp [valueResult] at tailSuccess
            | ok valuePair =>
                rcases valuePair with ⟨inferredValue, finalState⟩
                simp only [valueResult, pure, Pure.pure, Except.pure]
                  at tailSuccess
                injection tailSuccess with resultEq
                injection resultEq with _ valueStateEq
                injection valueStateEq with _ finalEq
                subst final
                exact expressionLedger valueResult
                  (placeTracked.unify unifyResult)
      cases operator with
      | equal =>
          simp only [pure, Pure.pure, Except.pure] at success
          cases valueResult : Detail.inferExprFuel fuel context value
              (some (placeState.resolve place.type)) placeState with
          | error error => simp [valueResult] at success
          | ok valuePair =>
              rcases valuePair with ⟨inferredValue, finalState⟩
              simp only [valueResult] at success
              injection success with resultEq
              injection resultEq with _ valueStateEq
              injection valueStateEq with _ finalEq
              subst final
              exact expressionLedger valueResult placeTracked
      | add => exact finishNonEqual success
      | subtract => exact finishNonEqual success
      | multiply => exact finishNonEqual success
      | divide => exact finishNonEqual success
      | modulo => exact finishNonEqual success
      | bitAnd => exact finishNonEqual success
      | bitXor => exact finishNonEqual success
      | bitOr => exact finishNonEqual success
      | shiftLeft => exact finishNonEqual success
      | shiftRight => exact finishNonEqual success
      | uncheckedAdd => exact finishNonEqual success
      | uncheckedSubtract => exact finishNonEqual success
      | uncheckedMultiply => exact finishNonEqual success
      | uncheckedDivide => exact finishNonEqual success
      | uncheckedModulo => exact finishNonEqual success

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementFamilyLedgerInvariant
/-!
The statement-side family of pending-template ledger preservation theorems.
This groups the fuel-mutual statement, statement-list, for-header and match-arm
steps without depending on the expression-side implementation module.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- All mutually dependent statement-side traversals at one fuel. -/
structure StatementFamilyLedgerPreservation (fuel : Nat) : Prop where
  statement : InferStatementFuelLedgerPreservation fuel
  statements : InferStatementsFuelLedgerPreservation fuel
  forItem : InferForItemFuelLedgerPreservation fuel
  forItems : InferForItemsFuelLedgerPreservation fuel
  matchCases : InferMatchCasesFuelLedgerPreservation fuel

/-- The whole statement-side family at fuel `n` depends only on expression,
place, assignment and pattern preservation at smaller fuel, plus the already
established statement-side family at smaller fuel.  The same-fuel `for` item
list is closed by structural list induction after its one-item theorem. -/
theorem statementFamilyLedgerPreservation_step
    {fuel : Nat}
    (exprPrev : ∀ childFuel, childFuel < fuel →
      InferExprFuelLedgerPreservation childFuel)
    (exprsPrev : ∀ childFuel, childFuel < fuel →
      InferExprsFuelLedgerPreservation childFuel)
    (placePrev : ∀ childFuel, childFuel < fuel →
      InferPlaceFuelLedgerPreservation childFuel)
    (assignedPrev : ∀ childFuel, childFuel < fuel →
      InferAssignedValueFuelLedgerPreservation childFuel)
    (patternPrev : ∀ childFuel, childFuel < fuel →
      ∀ {context : Frontend.SourceInference.Context}
        {pattern : Syntax.Pattern} {expected : Ty}
        {initial final : State} {inferred : TypedMatchPattern}
        {pending : List RequirementId},
        Detail.inferMatchPatternFuel childFuel context pattern expected
          initial = .ok (inferred, final) →
        RecursiveLedgerInvariant initial pending →
        RecursiveLedgerInvariant final pending)
    (familyPrev : ∀ childFuel, childFuel < fuel →
      StatementFamilyLedgerPreservation childFuel) :
    StatementFamilyLedgerPreservation fuel := by
  cases fuel with
  | zero =>
      have statementZero : InferStatementFuelLedgerPreservation 0 := by
        intro context statement expectedReturn initial result pending success
          tracked
        simp [Detail.inferStatementFuel] at success
      have statementsZero : InferStatementsFuelLedgerPreservation 0 := by
        intro context statements expectedReturn initial result pending success
          tracked
        simp [Detail.inferStatementsFuel] at success
      have forItemZero : InferForItemFuelLedgerPreservation 0 := by
        intro context item initial final inferred pending success tracked
        simp [Detail.inferForItemFuel] at success
      have casesZero : InferMatchCasesFuelLedgerPreservation 0 := by
        intro context scrutineeType expectedReturn outerScope cases initial
          result pending success tracked
        simp [Detail.inferMatchCasesFuel] at success
      exact ⟨statementZero, statementsZero, forItemZero,
        inferForItemsFuelLedgerPreservation_of_itemSoundness forItemZero,
        casesZero⟩
  | succ childFuel =>
      have previous := familyPrev childFuel (Nat.lt_succ_self childFuel)
      have itemCurrent : InferForItemFuelLedgerPreservation
          (childFuel + 1) :=
        inferForItemFuelLedgerPreservation_step
          (exprPrev childFuel (Nat.lt_succ_self childFuel))
          (placePrev childFuel (Nat.lt_succ_self childFuel))
          (assignedPrev childFuel (Nat.lt_succ_self childFuel))
      have itemsCurrent : InferForItemsFuelLedgerPreservation
          (childFuel + 1) :=
        inferForItemsFuelLedgerPreservation_of_itemSoundness itemCurrent
      have statementCurrent : InferStatementFuelLedgerPreservation
          (childFuel + 1) :=
        inferStatementFuelLedgerPreservation_step
          (exprPrev childFuel (Nat.lt_succ_self childFuel))
          (exprsPrev childFuel (Nat.lt_succ_self childFuel))
          previous.statements previous.forItems
          (placePrev childFuel (Nat.lt_succ_self childFuel))
          (assignedPrev childFuel (Nat.lt_succ_self childFuel))
          previous.matchCases
      have statementsCurrent : InferStatementsFuelLedgerPreservation
          (childFuel + 1) :=
        inferStatementsFuelLedgerPreservation_step
          (fun prior priorBound => (familyPrev prior priorBound).statement)
          (fun prior priorBound => (familyPrev prior priorBound).statements)
      have casesCurrent : InferMatchCasesFuelLedgerPreservation
          (childFuel + 1) :=
        inferMatchCasesFuelLedgerPreservation_step
          (patternPrev childFuel (Nat.lt_succ_self childFuel))
          previous.statements previous.matchCases
      exact ⟨statementCurrent, statementsCurrent, itemCurrent, itemsCurrent,
        casesCurrent⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end
