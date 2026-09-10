import Solcore.Frontend.ClosedSourceEvaluatorMonotonicityProperties
import Solcore.Frontend.ClosedSourceEvaluatorCompletenessProperties

/- Finite original derivations have a positive exact depth cutoff, not a total search bound. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem exact_threshold_of_success {α : Type} (f : Nat → Option α)
    (zero : f 0 = none)
    (monotone : ∀ {small large value}, small ≤ large →
      f small = some value → f large = some value)
    {budget : Nat} {value : α} (accepted : f budget = some value) :
    ∃ required : Nat, 0 < required ∧ ∀ n,
      f n = if required ≤ n then some value else none := by
  induction budget with
  | zero => rw [zero] at accepted; cases accepted
  | succ budget ih =>
      cases previous : f budget with
      | none =>
          refine ⟨budget + 1, Nat.zero_lt_succ _, ?_⟩
          intro n
          by_cases order : budget + 1 ≤ n
          · simp only [if_pos order]
            exact monotone order accepted
          · simp only [if_neg order]
            cases actual : f n with
            | none => rfl
            | some result =>
                have impossible := monotone (show n ≤ budget by omega) actual
                rw [previous] at impossible
                cases impossible
      | some result =>
          have same : result = value :=
            Option.some.inj ((monotone (Nat.le_succ budget) previous).symm.trans accepted)
          subst result
          exact ih previous

/-- A finite original expression derivation has a positive, hole-free successful-depth range. -/
theorem ClosedSourceExpressionEvaluates.exact_depth_threshold
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore finalStore : List RuntimeValue}
    {source : Syntax.Expr} {value : RuntimeValue}
    (evaluated : ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore) :
    ∃ required : Nat, 0 < required ∧ ∀ budget,
      evaluateClosedSourceExpression? budget owner names captured initialStore source =
        if required ≤ budget then some (value, finalStore) else none := by
  obtain ⟨budget, accepted⟩ := evaluateClosedSourceExpression?_eventually_complete evaluated
  apply exact_threshold_of_success
    (fun n => evaluateClosedSourceExpression? n owner names captured initialStore source)
    (by simp only [evaluateClosedSourceExpression?]) ?_ (accepted budget (Nat.le_refl _))
  intro small large endpoint order result
  obtain ⟨actual, actualStore⟩ := endpoint
  exact evaluateClosedSourceExpression?_monotone order result

/-- A finite original body derivation has a positive, hole-free successful-depth range. -/
theorem ClosedSourceBodyEvaluates.exact_depth_threshold
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore finalStore : List RuntimeValue}
    {source : Syntax.Block} {value : RuntimeValue}
    (evaluated : ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore) :
    ∃ required : Nat, 0 < required ∧ ∀ budget,
      evaluateClosedSourceBody? budget owner names captured initialStore source =
        if required ≤ budget then some (value, finalStore) else none := by
  obtain ⟨budget, accepted⟩ := evaluateClosedSourceBody?_eventually_complete evaluated
  apply exact_threshold_of_success
    (fun n => evaluateClosedSourceBody? n owner names captured initialStore source)
    (by simp only [evaluateClosedSourceBody?]) ?_ (accepted budget (Nat.le_refl _))
  intro small large endpoint order result
  obtain ⟨actual, actualStore⟩ := endpoint
  exact evaluateClosedSourceBody?_monotone order result

end Solcore.Frontend
