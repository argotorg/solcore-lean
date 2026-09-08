import Solcore.Frontend.LocalExpressionCost

/-! Raw source evaluation and independent transition costs have the same
successful outcomes. Joint uniqueness is proved on source derivations, so
skipped unresolved or unsupported syntax needs no Core translation. -/

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
  | bitAnd _ _ leftIH rightIH => exact .bitAnd leftIH rightIH
  | bitOr _ _ leftIH rightIH => exact .bitOr leftIH rightIH
  | bitXor _ _ leftIH rightIH => exact .bitXor leftIH rightIH
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

/-- Value, final store, and cost are jointly determined without whole source
resolution or typing. Incompatible branch choices contradict child uniqueness. -/
theorem LocalExpressionEvaluatesWithCost.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source left leftStore leftCost)
    (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  induction leftEvaluation generalizing right rightStore rightCost with
  | identifier named found =>
      cases rightEvaluation with
      | identifier otherNamed otherFound =>
          cases named.id_unique otherNamed
          exact ⟨found.value_unique otherFound, rfl, rfl⟩
  | wordLiteral meaning =>
      cases rightEvaluation with
      | wordLiteral otherMeaning =>
          cases meaning.value_unique otherMeaning
          exact ⟨rfl, rfl, rfl⟩
  | group _ ih =>
      cases rightEvaluation with
      | group child => exact ih child
  | logicalNot _ ih =>
      cases rightEvaluation with
      | logicalNot child =>
          obtain ⟨same, storeEq, rfl⟩ := ih child
          cases same
          exact ⟨rfl, storeEq, rfl⟩
  | bitNot _ ih =>
      cases rightEvaluation with
      | bitNot child =>
          obtain ⟨same, storeEq, rfl⟩ := ih child
          cases same
          exact ⟨rfl, storeEq, rfl⟩
  | bitAnd _ _ leftIH rightIH =>
      cases rightEvaluation with
      | bitAnd leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | bitOr _ _ leftIH rightIH =>
      cases rightEvaluation with
      | bitOr leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | bitXor _ _ leftIH rightIH =>
      cases rightEvaluation with
      | bitXor leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | andTrue _ _ leftIH rightIH =>
      cases rightEvaluation with
      | andTrue leftChild rightChild =>
          obtain ⟨_, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨same, storeEq, rfl⟩ := rightIH rightChild
          exact ⟨same, storeEq, rfl⟩
      | andFalse leftChild =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | andFalse _ leftIH =>
      cases rightEvaluation with
      | andFalse leftChild =>
          obtain ⟨_, storeEq, rfl⟩ := leftIH leftChild
          exact ⟨rfl, storeEq, rfl⟩
      | andTrue leftChild _ =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | orTrue _ leftIH =>
      cases rightEvaluation with
      | orTrue leftChild =>
          obtain ⟨_, storeEq, rfl⟩ := leftIH leftChild
          exact ⟨rfl, storeEq, rfl⟩
      | orFalse leftChild _ =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | orFalse _ _ leftIH rightIH =>
      cases rightEvaluation with
      | orFalse leftChild rightChild =>
          obtain ⟨_, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨same, storeEq, rfl⟩ := rightIH rightChild
          exact ⟨same, storeEq, rfl⟩
      | orTrue leftChild =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | ifTrue _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifTrue condition branch =>
          obtain ⟨_, rfl, rfl⟩ := conditionIH condition
          obtain ⟨same, storeEq, rfl⟩ := branchIH branch
          exact ⟨same, storeEq, rfl⟩
      | ifFalse condition _ =>
          obtain ⟨impossible, _⟩ := conditionIH condition
          cases impossible
  | ifFalse _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifFalse condition branch =>
          obtain ⟨_, rfl, rfl⟩ := conditionIH condition
          obtain ⟨same, storeEq, rfl⟩ := branchIH branch
          exact ⟨same, storeEq, rfl⟩
      | ifTrue condition _ =>
          obtain ⟨impossible, _⟩ := conditionIH condition
          cases impossible

theorem LocalExpressionEvaluatesWithCost.cost_unique {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source left leftStore leftCost)
    (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source right rightStore rightCost) : leftCost = rightCost :=
  (leftEvaluation.deterministic rightEvaluation).2.2

end Solcore.Frontend
