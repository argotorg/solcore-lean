import Solcore.Frontend.LocalExpressionCostProperties

/-! The current source fragment neither reads nor writes the store. Replaying
an independent derivation preserves its value and cost on any replacement store.
This is stronger than preserving one store, and does not concern arbitrary Core. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalExpressionEvaluatesWithCost.change_store
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost)
    (replacement : Core.Store) :
    LocalExpressionEvaluatesWithCost table environment replacement source value replacement cost := by
  induction evaluation with
  | identifier named found => exact .identifier named found
  | wordLiteral meaning => exact .wordLiteral meaning
  | group _ ih => exact .group ih
  | logicalNot _ ih => exact .logicalNot ih
  | bitNot _ ih => exact .bitNot ih
  | add _ _ leftIH rightIH => exact .add leftIH rightIH
  | subtract _ _ leftIH rightIH => exact .subtract leftIH rightIH
  | multiply _ _ leftIH rightIH => exact .multiply leftIH rightIH
  | bitAnd _ _ leftIH rightIH => exact .bitAnd leftIH rightIH
  | bitOr _ _ leftIH rightIH => exact .bitOr leftIH rightIH
  | bitXor _ _ leftIH rightIH => exact .bitXor leftIH rightIH
  | greater _ _ leftIH rightIH => exact .greater leftIH rightIH
  | equal _ _ leftIH rightIH => exact .equal leftIH rightIH
  | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
  | andFalse _ ih => exact .andFalse ih
  | orTrue _ ih => exact .orTrue ih
  | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
  | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
  | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH

/-- No whole-expression typing or resolution is needed to replay raw evaluation;
in particular, this preserves the existing selected-branch-only boundary. -/
theorem LocalExpressionEvaluates.change_store
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value}
    (evaluation : LocalExpressionEvaluates table environment initialStore source value finalStore)
    (replacement : Core.Store) :
    LocalExpressionEvaluates table environment replacement source value replacement := by
  obtain ⟨_, costed⟩ := evaluation.exists_cost
  exact (costed.change_store replacement).erase

theorem localExpressionEvaluatesWithCost_store_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat} :
    LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost ↔
      finalStore = initialStore ∧
        LocalExpressionEvaluatesWithCost table environment replacement source value replacement cost := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

theorem localExpressionEvaluates_store_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {source : Syntax.Expr} {value : Core.Value} :
    LocalExpressionEvaluates table environment initialStore source value finalStore ↔
      finalStore = initialStore ∧ LocalExpressionEvaluates table environment replacement source value replacement := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

end Solcore.Frontend
