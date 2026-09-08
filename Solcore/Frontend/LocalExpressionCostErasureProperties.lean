import Solcore.Frontend.LocalExpressionCost

/-! Raw source evaluation and independent transition costs have the same
successful outcomes. Erasure and cost existence need no Core translation,
including evaluations with skipped unresolved or unsupported syntax. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalExpressionEvaluatesWithCost.erase {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost) :
    LocalExpressionEvaluates table environment initialStore source value finalStore := by
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
  | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
  | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
  | andFalse _ ih => exact .andFalse ih
  | orTrue _ ih => exact .orTrue ih
  | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
  | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
  | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH

theorem LocalExpressionEvaluates.exists_cost {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value}
    (evaluation : LocalExpressionEvaluates table environment initialStore source value finalStore) :
    ∃ cost, LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost := by
  induction evaluation with
  | identifier named found => exact ⟨1, .identifier named found⟩
  | wordLiteral meaning => exact ⟨1, .wordLiteral meaning⟩
  | group _ ih =>
      obtain ⟨cost, child⟩ := ih
      exact ⟨_, .group child⟩
  | logicalNot _ ih =>
      obtain ⟨cost, child⟩ := ih
      exact ⟨_, .logicalNot child⟩
  | bitNot _ ih =>
      obtain ⟨cost, child⟩ := ih
      exact ⟨_, .bitNot child⟩
  | add _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .add left right⟩
  | subtract _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .subtract left right⟩
  | multiply _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .multiply left right⟩
  | bitAnd _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .bitAnd left right⟩
  | bitOr _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .bitOr left right⟩
  | bitXor _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .bitXor left right⟩
  | greater _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .greater left right⟩
  | equal _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .equal left right⟩
  | notEqual _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .notEqual left right⟩
  | andTrue _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .andTrue left right⟩
  | andFalse _ ih =>
      obtain ⟨cost, child⟩ := ih
      exact ⟨_, .andFalse child⟩
  | orTrue _ ih =>
      obtain ⟨cost, child⟩ := ih
      exact ⟨_, .orTrue child⟩
  | orFalse _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .orFalse left right⟩
  | ifTrue _ _ conditionIH branchIH =>
      obtain ⟨conditionCost, condition⟩ := conditionIH
      obtain ⟨branchCost, branch⟩ := branchIH
      exact ⟨_, .ifTrue condition branch⟩
  | ifFalse _ _ conditionIH branchIH =>
      obtain ⟨conditionCost, condition⟩ := conditionIH
      obtain ⟨branchCost, branch⟩ := branchIH
      exact ⟨_, .ifFalse condition branch⟩

theorem localExpressionEvaluates_iff_exists_cost {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} :
    LocalExpressionEvaluates table environment initialStore source value finalStore ↔
      ∃ cost, LocalExpressionEvaluatesWithCost table environment
        initialStore source value finalStore cost :=
  ⟨LocalExpressionEvaluates.exists_cost, fun ⟨_, evaluation⟩ => evaluation.erase⟩

theorem LocalExpressionEvaluatesWithCost.store_eq {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost) : finalStore = initialStore :=
  evaluation.erase.store_eq

theorem LocalExpressionEvaluatesWithCost.cost_pos {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost) : 0 < cost := by
  induction evaluation <;> omega

end Solcore.Frontend
