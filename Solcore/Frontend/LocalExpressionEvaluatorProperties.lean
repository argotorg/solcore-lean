import Solcore.Frontend.LocalExpressionEvaluatorSoundnessProperties
import Solcore.Frontend.LocalExpressionEvaluatorCompletenessProperties
import Solcore.Frontend.LocalExpressionCostErasureProperties

/-! Exact optional results characterize raw source evaluation, not acceptance.
The store-free result does not erase a general derivation's store equality. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateLocalExpressionWithCost?_iff {table : LocalNameTable}
    {environment : Resolved.Environment} {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (store : Core.Store) :
    evaluateLocalExpressionWithCost? table environment source = some (value, cost) ↔
      LocalExpressionEvaluatesWithCost table environment store source value store cost :=
  ⟨fun accepted => evaluateLocalExpressionWithCost?_sound accepted store,
    evaluateLocalExpressionWithCost?_complete⟩

theorem localExpressionEvaluatesWithCost_iff_evaluate {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat} :
    LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost ↔
      finalStore = initialStore ∧
        evaluateLocalExpressionWithCost? table environment source = some (value, cost) := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluateLocalExpressionWithCost?_complete evaluation⟩
  · rintro ⟨rfl, accepted⟩
    exact evaluateLocalExpressionWithCost?_sound accepted _

theorem evaluateLocalExpressionWithCost?_eq_none_iff {table : LocalNameTable}
    {environment : Resolved.Environment} {source : Syntax.Expr} (store : Core.Store) :
    evaluateLocalExpressionWithCost? table environment source = none ↔
      ¬ ∃ value cost, LocalExpressionEvaluatesWithCost table environment store source value store cost := by
  constructor
  · intro absent ⟨value, cost, evaluation⟩
    have accepted := evaluateLocalExpressionWithCost?_complete evaluation
    rw [absent] at accepted
    cases accepted
  · intro absent
    cases result : evaluateLocalExpressionWithCost? table environment source with
    | none => rfl
    | some pair =>
        exact False.elim (absent ⟨pair.1, pair.2, evaluateLocalExpressionWithCost?_sound result store⟩)

theorem evaluateLocalExpressionWithCost?_exists_cost_iff {table : LocalNameTable}
    {environment : Resolved.Environment} {source : Syntax.Expr} {value : Core.Value}
    (store : Core.Store) :
    (∃ cost, evaluateLocalExpressionWithCost? table environment source = some (value, cost)) ↔
      LocalExpressionEvaluates table environment store source value store := by
  constructor
  · rintro ⟨cost, accepted⟩
    exact (evaluateLocalExpressionWithCost?_sound accepted store).erase
  · intro evaluation
    obtain ⟨cost, costed⟩ := evaluation.exists_cost
    exact ⟨cost, evaluateLocalExpressionWithCost?_complete costed⟩

theorem evaluateLocalExpressionWithCost?_value_iff {table : LocalNameTable}
    {environment : Resolved.Environment} {source : Syntax.Expr} {value : Core.Value}
    (store : Core.Store) :
    (evaluateLocalExpressionWithCost? table environment source).map Prod.fst = some value ↔
      LocalExpressionEvaluates table environment store source value store := by
  constructor
  · intro projected
    obtain ⟨⟨actual, cost⟩, accepted, same⟩ := Option.map_eq_some_iff.mp projected
    cases same
    exact (evaluateLocalExpressionWithCost?_sound accepted store).erase
  · intro evaluation
    obtain ⟨cost, accepted⟩ := (evaluateLocalExpressionWithCost?_exists_cost_iff store).mpr evaluation
    simp only [accepted, Option.map_some]

end Solcore.Frontend
