import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RecursiveLocalComputationEvaluation
import Solcore.Frontend.LocalExpressionCostCorrespondence
import Solcore.Frontend.LocalFunctionApplicationStepComposition

/-! Private original-root cost inversions reconcile overlapping pure derivations.
The existing continuation law preserves actual selected values, stores and costs. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem reflects_pure_cost {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost)
    {resolved : Resolved.Expr} (resolution : ResolvesLocalExpression table source resolved) :
    LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost := by
  induction evaluation generalizing resolved with
  | pure child => exact child
  | group _ ih =>
      cases resolution with
      | group child => exact .group (ih child)
  | application _ _ _ _ _ => cases resolution
  | @binary initialStore middleStore finalStore span operatorSpan left right sourceOp op
      leftValue rightValue result leftCost rightCost operator _ _ applied leftIH rightIH =>
      cases operator <;> cases resolution
      all_goals
        rename_i leftResolution rightResolution
        cases leftValue <;> cases rightValue <;> cases applied
        first
        | exact .add (leftIH leftResolution) (rightIH rightResolution)
        | exact .subtract (leftIH leftResolution) (rightIH rightResolution)
        | exact .multiply (leftIH leftResolution) (rightIH rightResolution)
        | exact .divide (leftIH leftResolution) (rightIH rightResolution)
        | exact .modulo (leftIH leftResolution) (rightIH rightResolution)
        | exact .bitAnd (leftIH leftResolution) (rightIH rightResolution)
        | exact .bitOr (leftIH leftResolution) (rightIH rightResolution)
        | exact .bitXor (leftIH leftResolution) (rightIH rightResolution)
        | exact .greater (leftIH leftResolution) (rightIH rightResolution)
        | exact .equal (leftIH leftResolution) (rightIH rightResolution)
  | ifTrue _ _ conditionIH branchIH =>
      cases resolution with
      | conditional condition yes _ => exact .ifTrue (conditionIH condition) (branchIH yes)
  | ifFalse _ _ conditionIH branchIH =>
      cases resolution with
      | conditional condition _ no => exact .ifFalse (conditionIH condition) (branchIH no)

  | logicalNot _ ih =>
      cases resolution with
      | logicalNot child => exact .logicalNot (ih child)
  | bitNot _ ih =>
      cases resolution with
      | bitNot child => exact .bitNot (ih child)

  | andTrue _ _ leftIH rightIH =>
      cases resolution with
      | logicalAnd left right => exact .andTrue (leftIH left) (rightIH right)
  | andFalse _ leftIH =>
      cases resolution with
      | logicalAnd left _ => exact .andFalse (leftIH left)
  | orTrue _ leftIH =>
      cases resolution with
      | logicalOr left _ => exact .orTrue (leftIH left)
  | orFalse _ _ leftIH rightIH =>
      cases resolution with
      | logicalOr left right => exact .orFalse (leftIH left) (rightIH right)

private theorem reflects_binary_cost {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
    {value : Core.Value} {cost : Nat} (operator : DirectWordBinary sourceOp op)
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment initialStore
      ⟨span, .binary left ⟨operatorSpan, sourceOp⟩ right⟩ value finalStore cost) :
    ∃ middleStore leftValue rightValue leftCost rightCost,
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore left leftValue middleStore leftCost ∧
      RecursiveLocalComputationEvaluatesWithCost table environment middleStore right rightValue finalStore rightCost ∧
      op.apply leftValue rightValue = some value ∧ cost = leftCost + rightCost + 3 := by
  cases evaluation with
  | pure child =>
      cases operator <;> cases child
      all_goals exact ⟨_, _, _, _, _, .pure ‹_›, .pure ‹_›, rfl, rfl⟩
  | binary otherOperator leftChild rightChild applied =>
      cases operator <;> cases otherOperator
      all_goals exact ⟨_, _, _, _, _, leftChild, rightChild, applied, rfl⟩

  | andTrue _ _ => cases operator
  | andFalse _ => cases operator
  | orTrue _ => cases operator
  | orFalse _ _ => cases operator

private theorem reflects_conditional_cost {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {span question colon : Syntax.SourceSpan}
    {condition thenBranch elseBranch : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment initialStore
      ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore cost) :
    (∃ middleStore conditionCost branchCost,
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore condition (.bool true) middleStore conditionCost ∧
      RecursiveLocalComputationEvaluatesWithCost table environment middleStore thenBranch value finalStore branchCost ∧
      cost = conditionCost + branchCost + 2) ∨
    (∃ middleStore conditionCost branchCost,
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore condition (.bool false) middleStore conditionCost ∧
      RecursiveLocalComputationEvaluatesWithCost table environment middleStore elseBranch value finalStore branchCost ∧
      cost = conditionCost + branchCost + 2) := by
  cases evaluation with
  | pure child =>
      cases child with
      | ifTrue guard branch => exact .inl ⟨_, _, _, .pure guard, .pure branch, rfl⟩
      | ifFalse guard branch => exact .inr ⟨_, _, _, .pure guard, .pure branch, rfl⟩
  | ifTrue guard branch => exact .inl ⟨_, _, _, guard, branch, rfl⟩
  | ifFalse guard branch => exact .inr ⟨_, _, _, guard, branch, rfl⟩

private theorem reflects_logicalNot_cost {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
    {operand : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment initialStore
      ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩ value finalStore cost) :
    ∃ operandValue childCost,
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore operand (.bool operandValue) finalStore childCost ∧
      value = .bool (!operandValue) ∧ cost = childCost + 2 := by
  cases evaluation with
  | pure child => cases child with | logicalNot operand => exact ⟨_, _, .pure operand, rfl, rfl⟩
  | logicalNot child => exact ⟨_, _, child, rfl, rfl⟩

private theorem reflects_bitNot_cost {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
    {operand : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment initialStore
      ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩ value finalStore cost) :
    ∃ operandValue childCost,
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore operand (.word operandValue) finalStore childCost ∧
      value = .word operandValue.bitNot ∧ cost = childCost + 2 := by
  cases evaluation with
  | pure child => cases child with | bitNot operand => exact ⟨_, _, .pure operand, rfl, rfl⟩
  | bitNot child => exact ⟨_, _, child, rfl, rfl⟩

private theorem reflects_and_cost {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ value finalStore cost) :
    (∃ middleStore leftCost rightCost,
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore left (.bool true) middleStore leftCost ∧
      RecursiveLocalComputationEvaluatesWithCost table environment middleStore right value finalStore rightCost ∧
      cost = leftCost + rightCost + 2) ∨
    (∃ leftCost, RecursiveLocalComputationEvaluatesWithCost table environment initialStore left (.bool false) finalStore leftCost ∧
      value = .bool false ∧ cost = leftCost + 3) := by
  cases evaluation with
  | pure child =>
      cases child with
      | andTrue left right => exact .inl ⟨_, _, _, .pure left, .pure right, rfl⟩
      | andFalse left => exact .inr ⟨_, .pure left, rfl, rfl⟩
  | binary operator _ _ _ => cases operator
  | andTrue left right => exact .inl ⟨_, _, _, left, right, rfl⟩
  | andFalse left => exact .inr ⟨_, left, rfl, rfl⟩

private theorem reflects_or_cost {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ value finalStore cost) :
    (∃ leftCost, RecursiveLocalComputationEvaluatesWithCost table environment initialStore left (.bool true) finalStore leftCost ∧
      value = .bool true ∧ cost = leftCost + 3) ∨
    (∃ middleStore leftCost rightCost,
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore left (.bool false) middleStore leftCost ∧
      RecursiveLocalComputationEvaluatesWithCost table environment middleStore right value finalStore rightCost ∧
      cost = leftCost + rightCost + 2) := by
  cases evaluation with
  | pure child =>
      cases child with
      | orTrue left => exact .inl ⟨_, .pure left, rfl, rfl⟩
      | orFalse left right => exact .inr ⟨_, _, _, .pure left, .pure right, rfl⟩
  | binary operator _ _ _ => cases operator
  | orTrue left => exact .inl ⟨_, left, rfl, rfl⟩
  | orFalse left right => exact .inr ⟨_, _, _, left, right, rfl⟩

private theorem reflects_group_cost {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {span : Syntax.SourceSpan} {inner : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment initialStore
      ⟨span, .group inner⟩ value finalStore cost) :
    RecursiveLocalComputationEvaluatesWithCost table environment initialStore inner value finalStore cost := by
  cases evaluation with
  | pure child => cases child with | group inner => exact .pure inner
  | group child => exact child

theorem RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type)
    (sameIds : environment.ids = context.ids) (continuation : List Core.Frame) :
    Core.Steps cost ⟨.eval core environment.values, continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  induction elaboration generalizing initialStore finalStore value cost continuation with
  | pure resolution lowered _ =>
      rw [← sameIds] at lowered
      exact (reflects_pure_cost evaluation resolution).toStepsWithContinuation resolution lowered continuation
  | group _ ih => exact ih (reflects_group_cost evaluation) continuation
  | application _ _ functionIH argumentIH =>
      cases evaluation with
      | pure child => cases child
      | application functionEvaluation argumentEvaluation bodyPath =>
          exact CostStepComposition.apply (functionIH functionEvaluation _) (argumentIH argumentEvaluation _) bodyPath
  | binary operator _ _ leftIH rightIH =>
      obtain ⟨_, _, _, _, _, leftChild, rightChild, applied, rfl⟩ := reflects_binary_cost operator evaluation
      exact CostStepComposition.binary (leftIH leftChild _) (rightIH rightChild _) applied
  | conditional _ _ _ conditionIH thenIH elseIH =>
      rcases reflects_conditional_cost evaluation with ⟨_, _, _, guard, branch, rfl⟩ | ⟨_, _, _, guard, branch, rfl⟩
      · exact CostStepComposition.ifTrue (conditionIH guard _) (thenIH branch _)
      · exact CostStepComposition.ifFalse (conditionIH guard _) (elseIH branch _)

  | logicalNot _ ih =>
      obtain ⟨_, _, child, rfl, rfl⟩ := reflects_logicalNot_cost evaluation
      exact CostStepComposition.unary (ih child _) rfl
  | bitNot _ ih =>
      obtain ⟨_, _, child, rfl, rfl⟩ := reflects_bitNot_cost evaluation
      exact CostStepComposition.unary (ih child _) rfl

  | logicalAnd _ _ leftIH rightIH =>
      rcases reflects_and_cost evaluation with ⟨_, _, _, left, right, rfl⟩ | ⟨_, left, rfl, rfl⟩
      · exact CostStepComposition.ifTrue (leftIH left _) (rightIH right _)
      · simpa only [Nat.add_assoc] using CostStepComposition.ifFalse (leftIH left _) (.cons .bool .refl)
  | logicalOr _ _ leftIH rightIH =>
      rcases reflects_or_cost evaluation with ⟨_, left, rfl, rfl⟩ | ⟨_, _, _, left, right, rfl⟩
      · simpa only [Nat.add_assoc] using CostStepComposition.ifTrue (leftIH left _) (.cons .bool .refl)
      · exact CostStepComposition.ifFalse (leftIH left _) (rightIH right _)

end Solcore.Frontend
