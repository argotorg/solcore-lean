import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RecursiveLocalComputationEvaluationProperties
import Solcore.Frontend.LocalExpressionEvaluationProperties
import Solcore.Frontend.LocalExpressionCostCorrespondence
import Solcore.Frontend.LocalFunctionApplicationStepComposition

/-! Exact original provenance connects recursive calls to Core. Pure/group/binary
overlap changes neither successful observations nor their exact costs. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem reflects_group {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {span : Syntax.SourceSpan} {inner : Syntax.Expr} {value : Core.Value}
    (evaluation : RecursiveLocalComputationEvaluates table environment initialStore
      ⟨span, .group inner⟩ value finalStore) :
    RecursiveLocalComputationEvaluates table environment initialStore inner value finalStore := by
  cases evaluation with
  | pure child => cases child with | group inner => exact .pure inner
  | group child => exact child

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

private theorem reflects_pure {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value}
    (evaluation : RecursiveLocalComputationEvaluates table environment initialStore source value finalStore)
    {resolved : Resolved.Expr} (resolution : ResolvesLocalExpression table source resolved) :
    LocalExpressionEvaluates table environment initialStore source value finalStore := by
  obtain ⟨_, costed⟩ := recursiveLocalComputationEvaluates_iff_exists_cost.mp evaluation
  exact (reflects_pure_cost costed resolution).erase

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

private theorem reflects_group_cost {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {span : Syntax.SourceSpan} {inner : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment initialStore
      ⟨span, .group inner⟩ value finalStore cost) :
    RecursiveLocalComputationEvaluatesWithCost table environment initialStore inner value finalStore cost := by
  cases evaluation with
  | pure child => cases child with | group inner => exact .pure inner
  | group child => exact child

theorem RecursiveLocalComputationElaborates.evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type)
    (sameIds : environment.ids = context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    RecursiveLocalComputationEvaluates table environment initialStore source value finalStore ↔
      Core.Evaluates environment.values initialStore core value finalStore := by
  induction elaboration generalizing initialStore finalStore value with
  | pure resolution lowered _ =>
      rw [← sameIds] at lowered
      exact ⟨fun evaluation => (resolution.core_evaluates_iff lowered).mp (reflects_pure evaluation resolution),
        fun evaluation => .pure ((resolution.core_evaluates_iff lowered).mpr evaluation)⟩
  | group _ ih =>
      exact ⟨fun evaluation => ih.mp (reflects_group evaluation), fun evaluation => .group (ih.mpr evaluation)⟩
  | application _ _ functionIH argumentIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | pure child => cases child
        | application functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply (functionIH.mp functionEvaluation) (argumentIH.mp argumentEvaluation) bodyEvaluation
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .application (functionIH.mpr functionEvaluation) (argumentIH.mpr argumentEvaluation) bodyEvaluation
  | binary operator _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        obtain ⟨_, costed⟩ := recursiveLocalComputationEvaluates_iff_exists_cost.mp evaluation
        obtain ⟨_, _, _, _, _, leftChild, rightChild, applied, _⟩ := reflects_binary_cost operator costed
        exact .binary
          (leftIH.mp (recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_, leftChild⟩))
          (rightIH.mp (recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_, rightChild⟩)) applied
      · intro evaluation
        cases evaluation with
        | binary leftChild rightChild applied =>
            exact .binary operator (leftIH.mpr leftChild) (rightIH.mpr rightChild) applied

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

theorem RecursiveLocalComputationElaborates.evaluatesWithCost_iff_steps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type)
    (sameIds : environment.ids = context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    RecursiveLocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost ↔
      Core.Steps cost (.initial core environment.values initialStore) (.final value finalStore) := by
  constructor
  · intro evaluation
    exact evaluation.toStepsWithContinuation elaboration sameIds []
  · intro path
    have evaluation := (elaboration.evaluates_iff sameIds).mpr (Core.steps_from_initial_sound path)
    obtain ⟨actualCost, actual⟩ := recursiveLocalComputationEvaluates_iff_exists_cost.mp evaluation
    have sameCost := (path.final_unique (actual.toStepsWithContinuation elaboration sameIds [])).1
    exact sameCost.symm ▸ actual

end Solcore.Frontend
