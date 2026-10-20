import Solcore.SourceSemantics.SourceInferenceCoercionGraphFormation

/-! The committed rows retain formation from the actual selected coercion plan. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation
open Frontend SourceInference TypeSystem

private theorem requirementBatch_row_origin (state : State) (predicates : List ProgramPredicate)
    {row : Requirement} (member : row ∈ (state.addRequirementsWithIds predicates).2.requirements) :
    row ∈ state.requirements ∨ row.predicate ∈ predicates := by
  induction predicates generalizing state with
  | nil => exact .inl member
  | cons head tail ih =>
    rcases ih (state.addRequirementWithId head).2 member with old | new
    · rcases List.mem_append.mp old with old | fresh
      · exact .inl old
      · cases List.mem_singleton.mp fresh
        exact .inr List.mem_cons_self
    · exact .inr (List.mem_cons_of_mem _ new)

/-- A newly committed row is the actual primary predicate or one of the
actual method predicates of a selected step. -/
theorem committed_coercion_requirement_origin (state : State)
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

/-- A new ledger row is formed because its exact selected producer is formed. -/
theorem committed_coercion_new_formation {semantic : SourceSemantics.Context} {state : State}
    {steps : List Detail.PlannedCoercionStep}
    (stepsFormed : ∀ step ∈ steps, PlannedCoercionStepFormed semantic step)
    {row : Requirement}
    (member : row ∈ (Detail.commitCoercionPlan state steps).2.requirements)
    (fresh : row ∉ state.requirements) : PredicateAdmissible semantic row.predicate := by
  rcases committed_coercion_requirement_origin state steps member with old | new
  · exact (fresh old).elim
  · obtain ⟨step, stepMember, primary | method⟩ := new
    · exact primary ▸ (stepsFormed step stepMember).2.2.1
    · exact (stepsFormed step stepMember).2.2.2 row.predicate method

/-- Successful expected fitting either preserves the requirement ledger or
commits the actual search result. The normalized operand and expected type
are supplied by the enclosing expression derivation. -/
theorem withExpected_new_requirements_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {state : State} {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult}
    (formation : CoercionFormationContext semantic context)
    (actualFormed : TypeAdmissible semantic (state.resolve actual.type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (state.resolve type))
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateAdmissible semantic row.predicate := by
  cases expected with
  | none =>
    simp only [Detail.withExpected, Except.ok.injEq] at accepted
    cases accepted
    exact fun row member fresh => (fresh member).elim
  | some expected =>
    have expectedFormed := expectedFormed expected (by simp)
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
            exact fun _ member fresh => committed_coercion_new_formation
              (coercion_plan_formation formation actualFormed expectedFormed planned) member fresh

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
