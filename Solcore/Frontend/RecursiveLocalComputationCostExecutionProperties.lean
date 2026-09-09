import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RecursiveLocalComputationEvaluation
import Solcore.Frontend.LocalExpressionCostCorrespondence
import Solcore.Frontend.LocalFunctionApplicationStepComposition
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Frontend.WordLessCostStepComposition

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
  | notEqual _ _ leftIH rightIH =>
      cases resolution with
      | notEqual left right => exact .notEqual (leftIH left) (rightIH right)
  | lessEqual _ _ leftIH rightIH =>
      cases resolution with
      | lessEqual left right => exact .lessEqual (leftIH left) (rightIH right)

  | less _ _ leftIH rightIH =>
      cases resolution with
      | less left right => exact .less (leftIH left) (rightIH right)
  | greaterEqual _ _ leftIH rightIH =>
      cases resolution with
      | greaterEqual left right => exact .greaterEqual (leftIH left) (rightIH right)

private theorem ordered_path {environment : Core.Environment}
    {initialStore middleStore finalStore : Core.Store} {left right : Core.Expr}
    {leftWord rightWord : Core.Word} {leftCost rightCost : Nat}
    (rightFragment : RecursiveLocalComputationFragment right)
    (leftPath : ∀ continuation, Core.Steps leftCost
      ⟨.eval left environment, continuation, initialStore⟩
      ⟨.ret (.word leftWord), continuation, middleStore⟩)
    (rightPath : ∀ continuation, Core.Steps rightCost
      ⟨.eval right environment, continuation, middleStore⟩
      ⟨.ret (.word rightWord), continuation, finalStore⟩)
    (continuation : List Core.Frame) :
    Core.Steps (leftCost + rightCost + 9)
      ⟨.eval (left.wordLt right) environment, continuation, initialStore⟩
      ⟨.ret (.bool (decide (leftWord < rightWord))), continuation, finalStore⟩ := by
  obtain ⟨pairedCost, paired⟩ := rightFragment.insertion_paths [] environment (.word leftWord)
    (Core.steps_from_initial_sound (rightPath []))
  have sameCost : pairedCost = rightCost := ((paired []).1.final_unique (rightPath [])).1
  exact CostStepComposition.wordLt leftPath (fun k => sameCost ▸ (paired k).2) continuation

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
  | group _ ih =>
      cases evaluation with
      | pure child => cases child with | group inner => exact ih (.pure inner) continuation
      | group child => exact ih child continuation
  | application _ _ functionIH argumentIH =>
      cases evaluation with
      | pure child => cases child
      | application functionEvaluation argumentEvaluation bodyPath =>
          exact CostStepComposition.apply (functionIH functionEvaluation _) (argumentIH argumentEvaluation _) bodyPath
  | binary operator _ _ leftIH rightIH =>
      cases evaluation with
      | pure child =>
          cases operator <;> cases child
          all_goals exact CostStepComposition.binary (leftIH (.pure ‹_›) _) (rightIH (.pure ‹_›) _) rfl
      | binary otherOperator left right applied =>
          cases operator <;> cases otherOperator
          all_goals exact CostStepComposition.binary (leftIH left _) (rightIH right _) applied
      | andTrue _ _ | andFalse _ | orTrue _ | orFalse _ _ | notEqual _ _ | lessEqual _ _ | less _ _ | greaterEqual _ _ => cases operator
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | ifTrue guard branch => exact CostStepComposition.ifTrue (conditionIH (.pure guard) _) (thenIH (.pure branch) _)
          | ifFalse guard branch => exact CostStepComposition.ifFalse (conditionIH (.pure guard) _) (elseIH (.pure branch) _)
      | ifTrue guard branch => exact CostStepComposition.ifTrue (conditionIH guard _) (thenIH branch _)
      | ifFalse guard branch => exact CostStepComposition.ifFalse (conditionIH guard _) (elseIH branch _)
  | logicalNot _ ih =>
      cases evaluation with
      | pure child => cases child with | logicalNot operand => exact CostStepComposition.unary (ih (.pure operand) _) rfl
      | logicalNot child => exact CostStepComposition.unary (ih child _) rfl
  | bitNot _ ih =>
      cases evaluation with
      | pure child => cases child with | bitNot operand => exact CostStepComposition.unary (ih (.pure operand) _) rfl
      | bitNot child => exact CostStepComposition.unary (ih child _) rfl
  | logicalAnd _ _ leftIH rightIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | andTrue left right => exact CostStepComposition.ifTrue (leftIH (.pure left) _) (rightIH (.pure right) _)
          | andFalse left => simpa only [Nat.add_assoc] using CostStepComposition.ifFalse (leftIH (.pure left) _) (.cons .bool .refl)
      | binary operator _ _ _ => cases operator
      | andTrue left right => exact CostStepComposition.ifTrue (leftIH left _) (rightIH right _)
      | andFalse left => simpa only [Nat.add_assoc] using CostStepComposition.ifFalse (leftIH left _) (.cons .bool .refl)
  | logicalOr _ _ leftIH rightIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | orTrue left => simpa only [Nat.add_assoc] using CostStepComposition.ifTrue (leftIH (.pure left) _) (.cons .bool .refl)
          | orFalse left right => exact CostStepComposition.ifFalse (leftIH (.pure left) _) (rightIH (.pure right) _)
      | binary operator _ _ _ => cases operator
      | orTrue left => simpa only [Nat.add_assoc] using CostStepComposition.ifTrue (leftIH left _) (.cons .bool .refl)
      | orFalse left right => exact CostStepComposition.ifFalse (leftIH left _) (rightIH right _)
  | notEqual _ _ leftIH rightIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | notEqual left right =>
              simpa only [Nat.add_assoc] using CostStepComposition.unary (op := .boolNot)
                (CostStepComposition.binary (op := .wordEq) (leftIH (.pure left) _) (rightIH (.pure right) _) rfl) rfl
      | binary operator _ _ _ => cases operator
      | notEqual left right =>
          simpa only [Nat.add_assoc] using CostStepComposition.unary (op := .boolNot)
            (CostStepComposition.binary (op := .wordEq) (leftIH left _) (rightIH right _) rfl) rfl
  | lessEqual _ _ leftIH rightIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | lessEqual left right =>
              simpa only [Nat.add_assoc] using CostStepComposition.unary (op := .boolNot)
                (CostStepComposition.binary (op := .wordGt) (leftIH (.pure left) _) (rightIH (.pure right) _) rfl) rfl
      | binary operator _ _ _ => cases operator
      | lessEqual left right =>
          simpa only [Nat.add_assoc] using CostStepComposition.unary (op := .boolNot)
            (CostStepComposition.binary (op := .wordGt) (leftIH left _) (rightIH right _) rfl) rfl
  | less _ rightElab leftIH rightIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | less left right => exact ordered_path rightElab.core_fragment (leftIH (.pure left)) (rightIH (.pure right)) continuation
      | binary operator _ _ _ => cases operator
      | less left right => exact ordered_path rightElab.core_fragment (leftIH left) (rightIH right) continuation
  | greaterEqual _ rightElab leftIH rightIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | greaterEqual left right =>
              simpa only [Nat.add_assoc] using CostStepComposition.unary (op := .boolNot)
                (ordered_path rightElab.core_fragment (leftIH (.pure left)) (rightIH (.pure right)) _) rfl
      | binary operator _ _ _ => cases operator
      | greaterEqual left right =>
          simpa only [Nat.add_assoc] using CostStepComposition.unary (op := .boolNot)
            (ordered_path rightElab.core_fragment (leftIH left) (rightIH right) _) rfl

end Solcore.Frontend
