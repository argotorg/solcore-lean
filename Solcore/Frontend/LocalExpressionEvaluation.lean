import Solcore.Frontend.LocalExpressionEvaluationRules

/-! Determinism for independent source evaluation. The historical import path
continues to expose the evaluation rules and unchanged store law. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- No whole-resolution or typing premise is needed for source determinism. -/
theorem LocalExpressionEvaluates.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store}
    (leftEvaluation : LocalExpressionEvaluates table environment initialStore source left leftStore)
    (rightEvaluation : LocalExpressionEvaluates table environment initialStore source right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction leftEvaluation generalizing right rightStore with
  | identifier named found =>
      cases rightEvaluation with
      | identifier otherNamed otherFound =>
          cases named.id_unique otherNamed
          exact ⟨found.value_unique otherFound, rfl⟩
  | wordLiteral meaning =>
      cases rightEvaluation with
      | wordLiteral otherMeaning =>
          cases meaning.value_unique otherMeaning
          exact ⟨rfl, rfl⟩
  | group _ ih =>
      cases rightEvaluation with
      | group child => exact ih child
  | logicalNot _ ih =>
      cases rightEvaluation with
      | logicalNot child =>
          obtain ⟨same, storeEq⟩ := ih child
          cases same
          exact ⟨rfl, storeEq⟩
  | bitNot _ ih =>
      cases rightEvaluation with
      | bitNot child =>
          obtain ⟨same, storeEq⟩ := ih child
          cases same
          exact ⟨rfl, storeEq⟩
  | add _ _ leftIH rightIH =>
      cases rightEvaluation with
      | add leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | subtract _ _ leftIH rightIH =>
      cases rightEvaluation with
      | subtract leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | multiply _ _ leftIH rightIH =>
      cases rightEvaluation with
      | multiply leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | bitAnd _ _ leftIH rightIH =>
      cases rightEvaluation with
      | bitAnd leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | bitOr _ _ leftIH rightIH =>
      cases rightEvaluation with
      | bitOr leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | bitXor _ _ leftIH rightIH =>
      cases rightEvaluation with
      | bitXor leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | greater _ _ leftIH rightIH =>
      cases rightEvaluation with
      | greater leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | less _ _ leftIH rightIH =>
      cases rightEvaluation with
      | less leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | equal _ _ leftIH rightIH =>
      cases rightEvaluation with
      | equal leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | notEqual _ _ leftIH rightIH =>
      cases rightEvaluation with
      | notEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | lessEqual _ _ leftIH rightIH =>
      cases rightEvaluation with
      | lessEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | andTrue _ _ leftIH rightIH =>
      cases rightEvaluation with
      | andTrue leftChild rightChild =>
          obtain ⟨_, rfl⟩ := leftIH leftChild
          exact rightIH rightChild
      | andFalse leftChild =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | andFalse _ leftIH =>
      cases rightEvaluation with
      | andFalse leftChild => exact leftIH leftChild
      | andTrue leftChild _ =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | orTrue _ leftIH =>
      cases rightEvaluation with
      | orTrue leftChild => exact leftIH leftChild
      | orFalse leftChild _ =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | orFalse _ _ leftIH rightIH =>
      cases rightEvaluation with
      | orFalse leftChild rightChild =>
          obtain ⟨_, rfl⟩ := leftIH leftChild
          exact rightIH rightChild
      | orTrue leftChild =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | ifTrue _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifTrue condition branch =>
          obtain ⟨_, rfl⟩ := conditionIH condition
          exact branchIH branch
      | ifFalse condition _ =>
          obtain ⟨impossible, _⟩ := conditionIH condition
          cases impossible
  | ifFalse _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifFalse condition branch =>
          obtain ⟨_, rfl⟩ := conditionIH condition
          exact branchIH branch
      | ifTrue condition _ =>
          obtain ⟨impossible, _⟩ := conditionIH condition
          cases impossible

end Solcore.Frontend
