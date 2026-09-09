import Solcore.Frontend.RecursiveLocalComputationDeterminismProperties
import Solcore.Core.Correspondence

/-! Raw success and exact cost agree across overlapping pure and recursive
groups, direct/negated comparisons, conditionals and fixed lazy operators.
Actual closures, arguments and stores are fixed by evaluation,
not by a checker, type tags or a global restriction on skipped source syntax. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem erase {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment
      initialStore source value finalStore cost) :
    RecursiveLocalComputationEvaluates table environment initialStore source value finalStore := by
  induction evaluation with
  | pure child => exact .pure child.erase
  | group _ ih => exact .group ih
  | application _ _ bodyPath functionIH argumentIH =>
      exact .application functionIH argumentIH (Core.steps_from_initial_sound bodyPath)
  | binary operator _ _ applied leftIH rightIH =>
      exact .binary operator leftIH rightIH applied
  | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
  | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH
  | logicalNot _ ih => exact .logicalNot ih
  | bitNot _ ih => exact .bitNot ih
  | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
  | andFalse _ ih => exact .andFalse ih
  | orTrue _ ih => exact .orTrue ih
  | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
  | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
  | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH

private theorem exists_cost {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value}
    (evaluation : RecursiveLocalComputationEvaluates table environment
      initialStore source value finalStore) :
    ∃ cost, RecursiveLocalComputationEvaluatesWithCost table environment
      initialStore source value finalStore cost := by
  induction evaluation with
  | pure child =>
      obtain ⟨_, costed⟩ := child.exists_cost
      exact ⟨_, .pure costed⟩
  | group _ ih =>
      obtain ⟨_, costed⟩ := ih
      exact ⟨_, .group costed⟩
  | application _ _ bodyEvaluation functionIH argumentIH =>
      obtain ⟨_, functionCosted⟩ := functionIH
      obtain ⟨_, argumentCosted⟩ := argumentIH
      obtain ⟨_, bodyPath⟩ := bodyEvaluation.toSteps
      exact ⟨_, .application functionCosted argumentCosted bodyPath⟩
  | binary operator _ _ applied leftIH rightIH =>
      obtain ⟨_, leftCosted⟩ := leftIH
      obtain ⟨_, rightCosted⟩ := rightIH
      exact ⟨_, .binary operator leftCosted rightCosted applied⟩
  | ifTrue _ _ conditionIH branchIH =>
      obtain ⟨_, conditionCosted⟩ := conditionIH
      obtain ⟨_, branchCosted⟩ := branchIH
      exact ⟨_, .ifTrue conditionCosted branchCosted⟩
  | ifFalse _ _ conditionIH branchIH =>
      obtain ⟨_, conditionCosted⟩ := conditionIH
      obtain ⟨_, branchCosted⟩ := branchIH
      exact ⟨_, .ifFalse conditionCosted branchCosted⟩
  | logicalNot _ ih =>
      obtain ⟨_, costed⟩ := ih
      exact ⟨_, .logicalNot costed⟩
  | bitNot _ ih =>
      obtain ⟨_, costed⟩ := ih
      exact ⟨_, .bitNot costed⟩
  | andTrue _ _ leftIH rightIH =>
      obtain ⟨_, leftCosted⟩ := leftIH
      obtain ⟨_, rightCosted⟩ := rightIH
      exact ⟨_, .andTrue leftCosted rightCosted⟩
  | andFalse _ ih =>
      obtain ⟨_, costed⟩ := ih
      exact ⟨_, .andFalse costed⟩
  | orTrue _ ih =>
      obtain ⟨_, costed⟩ := ih
      exact ⟨_, .orTrue costed⟩
  | orFalse _ _ leftIH rightIH =>
      obtain ⟨_, leftCosted⟩ := leftIH
      obtain ⟨_, rightCosted⟩ := rightIH
      exact ⟨_, .orFalse leftCosted rightCosted⟩

  | notEqual _ _ leftIH rightIH =>
      obtain ⟨_, leftCosted⟩ := leftIH
      obtain ⟨_, rightCosted⟩ := rightIH
      exact ⟨_, .notEqual leftCosted rightCosted⟩
  | lessEqual _ _ leftIH rightIH =>
      obtain ⟨_, leftCosted⟩ := leftIH
      obtain ⟨_, rightCosted⟩ := rightIH
      exact ⟨_, .lessEqual leftCosted rightCosted⟩

theorem recursiveLocalComputationEvaluates_iff_exists_cost {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} :
    RecursiveLocalComputationEvaluates table environment initialStore source value finalStore ↔
      ∃ cost, RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore source value finalStore cost :=
  ⟨exists_cost, fun ⟨_, evaluation⟩ => erase evaluation⟩

end Solcore.Frontend
