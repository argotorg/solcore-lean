import Solcore.SourceSemantics.SourceInferenceStatementLedgerInvariant
import Solcore.SourceSemantics.SourceInferenceForItemsScopedSoundness

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
