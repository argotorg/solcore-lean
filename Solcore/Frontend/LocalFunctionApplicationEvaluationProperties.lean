import Solcore.Frontend.LocalFunctionApplicationEvaluation
import Solcore.Frontend.LocalExpressionCostProperties
import Solcore.Core.Correspondence
import Solcore.Core.ExactFuelProperties

/-! Successful source-call evaluation and exact costs retain the actual closure
and its store-threaded body. These laws need neither checking nor typed inputs. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalFunctionApplicationEvaluates.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store}
    (leftEvaluation : LocalFunctionApplicationEvaluates table environment initialStore source left leftStore)
    (rightEvaluation : LocalFunctionApplicationEvaluates table environment initialStore source right rightStore) :
    left = right ∧ leftStore = rightStore := by
  cases leftEvaluation with
  | call functionEvaluation argumentEvaluation bodyEvaluation =>
      cases rightEvaluation with
      | call otherFunction otherArgument otherBody =>
          obtain ⟨sameFunction, rfl⟩ := functionEvaluation.deterministic otherFunction
          cases sameFunction
          obtain ⟨rfl, rfl⟩ := argumentEvaluation.deterministic otherArgument
          exact Core.evaluation_deterministic bodyEvaluation otherBody

theorem LocalFunctionApplicationEvaluatesWithCost.erase {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source value finalStore cost) :
    LocalFunctionApplicationEvaluates table environment initialStore source value finalStore := by
  cases evaluation with
  | call functionEvaluation argumentEvaluation bodyPath =>
      exact .call functionEvaluation.erase argumentEvaluation.erase
        (Core.steps_from_initial_sound bodyPath)

theorem LocalFunctionApplicationEvaluates.exists_cost {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value}
    (evaluation : LocalFunctionApplicationEvaluates table environment initialStore source value finalStore) :
    ∃ cost, LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source value finalStore cost := by
  cases evaluation with
  | call functionEvaluation argumentEvaluation bodyEvaluation =>
      obtain ⟨_, functionCosted⟩ := functionEvaluation.exists_cost
      obtain ⟨_, argumentCosted⟩ := argumentEvaluation.exists_cost
      obtain ⟨_, bodyPath⟩ := bodyEvaluation.toSteps
      exact ⟨_, .call functionCosted argumentCosted bodyPath⟩

theorem localFunctionApplicationEvaluates_iff_exists_cost {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} :
    LocalFunctionApplicationEvaluates table environment initialStore source value finalStore ↔
      ∃ cost, LocalFunctionApplicationEvaluatesWithCost table environment
        initialStore source value finalStore cost :=
  ⟨LocalFunctionApplicationEvaluates.exists_cost, fun ⟨_, evaluation⟩ => evaluation.erase⟩

theorem LocalFunctionApplicationEvaluatesWithCost.cost_pos {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source value finalStore cost) : 0 < cost := by
  cases evaluation
  omega

/-- Child determinism fixes the actual closure and argument before comparing
the two closed paths for its body; no equality of static function tags is used. -/
theorem LocalFunctionApplicationEvaluatesWithCost.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (leftEvaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source left leftStore leftCost)
    (rightEvaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  cases leftEvaluation with
  | call functionEvaluation argumentEvaluation bodyPath =>
      cases rightEvaluation with
      | call otherFunction otherArgument otherPath =>
          obtain ⟨sameFunction, rfl, rfl⟩ := functionEvaluation.deterministic otherFunction
          cases sameFunction
          obtain ⟨rfl, rfl, rfl⟩ := argumentEvaluation.deterministic otherArgument
          obtain ⟨rfl, sameValue, sameStore⟩ := bodyPath.final_unique otherPath
          exact ⟨sameValue, sameStore, rfl⟩

theorem LocalFunctionApplicationEvaluatesWithCost.cost_unique {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (leftEvaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source left leftStore leftCost)
    (rightEvaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source right rightStore rightCost) : leftCost = rightCost :=
  (leftEvaluation.deterministic rightEvaluation).2.2

end Solcore.Frontend
