import Solcore.SourceSemantics.SourceInferenceStatementLedgerInvariant

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

end Solcore.SourceSemantics.SourceInferenceSoundness
