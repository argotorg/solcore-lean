import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyCoercions

/-! Actual committed coercion rows and expected-type continuations preserve
privacy of every newly generated predicate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem commit_inference (state : State) (steps : List Detail.PlannedCoercionStep) :
    (Detail.commitCoercionPlan state steps).2.inference = state.inference := by
  induction steps generalizing state with
  | nil => rfl
  | cons step rest ih =>
    simp only [Detail.commitCoercionPlan]
    rw [ih, requirementBatch_inference]
    rfl

/-- A newly committed row is the actual primary predicate or one of the
actual method predicates of a selected step. -/
theorem commitCoercionPlan_requirement_origin (state : State)
    (steps : List Detail.PlannedCoercionStep) {row : Requirement}
    (member : row ∈ (Detail.commitCoercionPlan state steps).2.requirements) :
    row ∈ state.requirements ∨ ∃ step ∈ steps,
      row.predicate = step.predicate ∨ row.predicate ∈ step.methodPredicates := by
  induction steps generalizing state with
  | nil => exact .inl member
  | cons step rest ih =>
    rcases ih _ member with old | fresh
    · rcases requirementBatch_row_origin _ _ old with old | method
      · rcases List.mem_append.mp old with old | primary
        · exact .inl old
        · cases List.mem_singleton.mp primary
          exact .inr ⟨step, List.mem_cons_self, .inl rfl⟩
      · exact .inr ⟨step, List.mem_cons_self, .inr method⟩
    · obtain ⟨origin, originMember, occurrence⟩ := fresh
      exact .inr ⟨origin, List.mem_cons_of_mem _ originMember, occurrence⟩

/-- The final allocation preserves the private predicate derived by search. -/
theorem commitCoercionPlan_new_private {protectedVars : List TypeVarId} {state : State}
    {steps : List Detail.PlannedCoercionStep}
    (stepsSafe : ∀ step ∈ steps, PlannedStepSafe protectedVars state step)
    {row : Requirement}
    (member : row ∈ (Detail.commitCoercionPlan state steps).2.requirements)
    (fresh : row ∉ state.requirements) :
    PredicateSafe protectedVars (Detail.commitCoercionPlan state steps).2 row.predicate := by
  rcases commitCoercionPlan_requirement_origin state steps member with old | new
  · exact (fresh old).elim
  · obtain ⟨step, stepMember, primary | method⟩ := new
    · have safe := (stepsSafe step stepMember).2.2.1
      rw [← primary] at safe
      simpa only [PredicateSafe, Safe, State.resolve, InferState.resolve, commit_inference] using safe
    · have safe := (stepsSafe step stepMember).2.2.2 row.predicate method
      simpa only [PredicateSafe, Safe, State.resolve, InferState.resolve, commit_inference] using safe

/-- Successful expected fitting either issues no rows or commits the actual
private path. The declaration catalog is checked at its genuine origin. -/
theorem withExpected_new_requirements_private
    {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {state : State} {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady)
    (actualSafe : Safe protectedVars state actual.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  cases expected with
  | none =>
    simp only [Detail.withExpected, Except.ok.injEq] at accepted
    cases accepted
    exact fun row member fresh => (fresh member).elim
  | some expected =>
    have expectedSafe := expectedSafe expected (by simp)
    cases unified : state.inference.unify actual.type expected with
    | ok inference =>
      simp only [Detail.withExpected, unified, Except.ok.injEq] at accepted
      cases accepted
      exact fun row member fresh => (fresh member).elim
    | error error =>
      cases error with
      | occursCheck _ _ => simp [Detail.withExpected, unified] at accepted
      | exhausted => simp [Detail.withExpected, unified] at accepted
      | mismatch left right =>
        simp only [Detail.withExpected, unified] at accepted
        cases planned : Detail.coercionPlan? context state
            (state.resolve actual.type) (state.resolve expected) with
        | error error => simp [planned, bind, Except.bind] at accepted
        | ok option =>
          cases option with
          | none => simp [planned, bind, Except.bind] at accepted
          | some plan =>
            simp only [planned, bind, Except.bind] at accepted
            change Except.ok _ = Except.ok result at accepted
            cases Except.ok.inj accepted
            exact fun _ member fresh => commitCoercionPlan_new_private
              (coercionPlan_private catalog (safe_resolved ready actualSafe)
                (safe_resolved ready expectedSafe) planned) member fresh

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
