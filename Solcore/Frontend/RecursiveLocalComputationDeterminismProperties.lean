import Solcore.Frontend.RecursiveLocalComputationEvaluation
import Solcore.Frontend.LocalExpressionCostProperties
import Solcore.Core.ExactFuelProperties

/-! Actual values, final stores and costs are jointly determined at every
original root, including pure overlap and skipped unsupported syntax. -/

set_option autoImplicit false

namespace Solcore.Frontend

-- The old pure relation has no root call, but may skip unsupported descendants.
-- Invert only the overlapping root; no global call-free premise is introduced.
private theorem agrees_with_pure {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore : Core.Store} {source : Syntax.Expr} {left right : Core.Value}
    {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment
      initialStore source left leftStore leftCost)
    (pureEvaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  induction evaluation generalizing right rightStore rightCost with
  | pure child => exact child.deterministic pureEvaluation
  | group _ ih =>
      cases pureEvaluation with
      | group child => exact ih child
  | application => cases pureEvaluation
  | binary operator _ _ applied leftIH rightIH =>
      cases operator <;> cases pureEvaluation
      all_goals
        rename_i pureLeft pureRight
        obtain ⟨rfl, rfl, rfl⟩ := leftIH pureLeft
        obtain ⟨rfl, rfl, rfl⟩ := rightIH pureRight
        cases applied
        exact ⟨rfl, rfl, rfl⟩
  | ifTrue _ _ conditionIH branchIH =>
      cases pureEvaluation with
      | ifTrue condition branch =>
          obtain ⟨_, rfl, rfl⟩ := conditionIH condition
          obtain ⟨rfl, rfl, rfl⟩ := branchIH branch
          exact ⟨rfl, rfl, rfl⟩
      | ifFalse condition _ => cases (conditionIH condition).1
  | ifFalse _ _ conditionIH branchIH =>
      cases pureEvaluation with
      | ifTrue condition _ => cases (conditionIH condition).1
      | ifFalse condition branch =>
          obtain ⟨_, rfl, rfl⟩ := conditionIH condition
          obtain ⟨rfl, rfl, rfl⟩ := branchIH branch
          exact ⟨rfl, rfl, rfl⟩

  | logicalNot _ ih =>
      cases pureEvaluation with
      | logicalNot child =>
          obtain ⟨sameValue, rfl, rfl⟩ := ih child
          cases sameValue
          exact ⟨rfl, rfl, rfl⟩
  | bitNot _ ih =>
      cases pureEvaluation with
      | bitNot child =>
          obtain ⟨sameValue, rfl, rfl⟩ := ih child
          cases sameValue
          exact ⟨rfl, rfl, rfl⟩
  | andTrue _ _ leftIH rightIH =>
      cases pureEvaluation with
      | andTrue left right =>
          obtain ⟨_, rfl, rfl⟩ := leftIH left
          obtain ⟨rfl, rfl, rfl⟩ := rightIH right
          exact ⟨rfl, rfl, rfl⟩
      | andFalse left => cases (leftIH left).1
  | andFalse _ ih =>
      cases pureEvaluation with
      | andTrue left _ => cases (ih left).1
      | andFalse left => obtain ⟨_, rfl, rfl⟩ := ih left; exact ⟨rfl, rfl, rfl⟩
  | orTrue _ ih =>
      cases pureEvaluation with
      | orTrue left => obtain ⟨_, rfl, rfl⟩ := ih left; exact ⟨rfl, rfl, rfl⟩
      | orFalse left _ => cases (ih left).1
  | orFalse _ _ leftIH rightIH =>
      cases pureEvaluation with
      | orTrue left => cases (leftIH left).1
      | orFalse left right =>
          obtain ⟨_, rfl, rfl⟩ := leftIH left
          obtain ⟨rfl, rfl, rfl⟩ := rightIH right
          exact ⟨rfl, rfl, rfl⟩

  | notEqual _ _ leftIH rightIH =>
      cases pureEvaluation with
      | notEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          cases sameLeft
          obtain ⟨sameRight, rfl, rfl⟩ := rightIH rightChild
          cases sameRight
          exact ⟨rfl, rfl, rfl⟩
  | lessEqual _ _ leftIH rightIH =>
      cases pureEvaluation with
      | lessEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          cases sameLeft
          obtain ⟨sameRight, rfl, rfl⟩ := rightIH rightChild
          cases sameRight
          exact ⟨rfl, rfl, rfl⟩

/-- Successful recursive derivations determine the actual value, final store
and cost jointly, including overlapping pure derivations and selected branches. -/
theorem RecursiveLocalComputationEvaluatesWithCost.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
      initialStore source left leftStore leftCost)
    (rightEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
      initialStore source right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  induction leftEvaluation generalizing right rightStore rightCost with
  | pure child =>
      obtain ⟨valueEq, storeEq, costEq⟩ := agrees_with_pure rightEvaluation child
      exact ⟨valueEq.symm, storeEq.symm, costEq.symm⟩
  | group child ih =>
      cases rightEvaluation with
      | pure other =>
          cases other with
          | group pureChild => exact agrees_with_pure child pureChild
      | group other => exact ih other
  | application _ _ bodyPath functionIH argumentIH =>
      cases rightEvaluation with
      | pure other => cases other
      | application otherFunction otherArgument otherPath =>
          obtain ⟨sameFunction, rfl, rfl⟩ := functionIH otherFunction
          cases sameFunction
          obtain ⟨rfl, rfl, rfl⟩ := argumentIH otherArgument
          obtain ⟨rfl, sameValue, sameStore⟩ := bodyPath.final_unique otherPath
          exact ⟨sameValue, sameStore, rfl⟩
  | binary operator leftChild rightChild applied leftIH rightIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.binary operator leftChild rightChild applied) other
      | binary otherOperator otherLeft otherRight otherApplied =>
          obtain ⟨rfl, rfl, rfl⟩ := leftIH otherLeft
          obtain ⟨rfl, rfl, rfl⟩ := rightIH otherRight
          cases operator <;> cases otherOperator
          all_goals exact ⟨Option.some.inj (applied.symm.trans otherApplied), rfl, rfl⟩
      | andTrue _ _ | andFalse _ | orTrue _ | orFalse _ _ | notEqual _ _ | lessEqual _ _ => cases operator
  | ifTrue condition branch conditionIH branchIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.ifTrue condition branch) other
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := conditionIH otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := branchIH otherBranch
          exact ⟨rfl, rfl, rfl⟩
      | ifFalse otherCondition _ => cases (conditionIH otherCondition).1
  | ifFalse condition branch conditionIH branchIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.ifFalse condition branch) other
      | ifTrue otherCondition _ => cases (conditionIH otherCondition).1
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := conditionIH otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := branchIH otherBranch
          exact ⟨rfl, rfl, rfl⟩

  | logicalNot child ih =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.logicalNot child) other
      | logicalNot other =>
          obtain ⟨sameValue, rfl, rfl⟩ := ih other
          cases sameValue
          exact ⟨rfl, rfl, rfl⟩
  | bitNot child ih =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.bitNot child) other
      | bitNot other =>
          obtain ⟨sameValue, rfl, rfl⟩ := ih other
          cases sameValue
          exact ⟨rfl, rfl, rfl⟩
  | andTrue leftChild rightChild leftIH rightIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.andTrue leftChild rightChild) other
      | binary operator _ _ _ => cases operator
      | andTrue otherLeft otherRight =>
          obtain ⟨_, rfl, rfl⟩ := leftIH otherLeft
          obtain ⟨rfl, rfl, rfl⟩ := rightIH otherRight
          exact ⟨rfl, rfl, rfl⟩
      | andFalse otherLeft => cases (leftIH otherLeft).1
  | andFalse left ih =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.andFalse left) other
      | binary operator _ _ _ => cases operator
      | andTrue otherLeft _ => cases (ih otherLeft).1
      | andFalse otherLeft => obtain ⟨_, rfl, rfl⟩ := ih otherLeft; exact ⟨rfl, rfl, rfl⟩
  | orTrue left ih =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.orTrue left) other
      | binary operator _ _ _ => cases operator
      | orTrue otherLeft => obtain ⟨_, rfl, rfl⟩ := ih otherLeft; exact ⟨rfl, rfl, rfl⟩
      | orFalse otherLeft _ => cases (ih otherLeft).1
  | orFalse leftChild rightChild leftIH rightIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.orFalse leftChild rightChild) other
      | binary operator _ _ _ => cases operator
      | orTrue otherLeft => cases (leftIH otherLeft).1
      | orFalse otherLeft otherRight =>
          obtain ⟨_, rfl, rfl⟩ := leftIH otherLeft
          obtain ⟨rfl, rfl, rfl⟩ := rightIH otherRight
          exact ⟨rfl, rfl, rfl⟩

  | notEqual leftChild rightChild leftIH rightIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.notEqual leftChild rightChild) other
      | binary operator _ _ _ => cases operator
      | notEqual otherLeft otherRight =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH otherLeft
          cases sameLeft
          obtain ⟨sameRight, rfl, rfl⟩ := rightIH otherRight
          cases sameRight
          exact ⟨rfl, rfl, rfl⟩
  | lessEqual leftChild rightChild leftIH rightIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.lessEqual leftChild rightChild) other
      | binary operator _ _ _ => cases operator
      | lessEqual otherLeft otherRight =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH otherLeft
          cases sameLeft
          obtain ⟨sameRight, rfl, rfl⟩ := rightIH otherRight
          cases sameRight
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Frontend
