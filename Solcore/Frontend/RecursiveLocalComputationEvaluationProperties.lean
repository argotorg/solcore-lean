import Solcore.Frontend.RecursiveLocalComputationEvaluation
import Solcore.Frontend.LocalExpressionCostProperties
import Solcore.Core.Correspondence
import Solcore.Core.ExactFuelProperties

/-! Raw success and exact cost agree even when old pure and recursive grouping
or direct binary evaluation overlap. Actual closures, arguments and stores are fixed by evaluation,
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

theorem recursiveLocalComputationEvaluates_iff_exists_cost {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} :
    RecursiveLocalComputationEvaluates table environment initialStore source value finalStore ↔
      ∃ cost, RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore source value finalStore cost :=
  ⟨exists_cost, fun ⟨_, evaluation⟩ => erase evaluation⟩

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

/-- Successful recursive derivations determine the actual value, final store
and cost jointly, including overlapping pure/group/binary derivations. -/
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

end Solcore.Frontend
