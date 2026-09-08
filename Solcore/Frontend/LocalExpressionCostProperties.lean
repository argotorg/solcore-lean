import Solcore.Frontend.LocalExpressionCostErasureProperties

/-! Joint uniqueness of independent source values, stores and transition costs.
The historical import path also retains erasure and cost-existence interfaces. -/

set_option autoImplicit false

namespace Solcore.Frontend

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
  | unit => cases rightEvaluation; exact ⟨rfl, rfl, rfl⟩
  | group _ ih =>
      cases rightEvaluation with
      | group child => exact ih child
  | pair _ _ leftIH rightIH =>
      cases rightEvaluation with
      | pair leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
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
  | add _ _ leftIH rightIH =>
      cases rightEvaluation with
      | add leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | subtract _ _ leftIH rightIH =>
      cases rightEvaluation with
      | subtract leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | multiply _ _ leftIH rightIH =>
      cases rightEvaluation with
      | multiply leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | divide _ _ leftIH rightIH =>
      cases rightEvaluation with
      | divide leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | modulo _ _ leftIH rightIH =>
      cases rightEvaluation with
      | modulo leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
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
  | greater _ _ leftIH rightIH =>
      cases rightEvaluation with
      | greater leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | less _ _ leftIH rightIH =>
      cases rightEvaluation with
      | less leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | equal _ _ leftIH rightIH =>
      cases rightEvaluation with
      | equal leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | notEqual _ _ leftIH rightIH =>
      cases rightEvaluation with
      | notEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | lessEqual _ _ leftIH rightIH =>
      cases rightEvaluation with
      | lessEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | greaterEqual _ _ leftIH rightIH =>
      cases rightEvaluation with
      | greaterEqual leftChild rightChild =>
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
