import Solcore.Frontend.LocalApplicationReturnBody
import Solcore.Frontend.LocalFunctionApplicationExecutionProperties

/-! Original singleton returns preserve their actual application's values,
stores and exact costs. Only exact Core correspondence requires aligned IDs. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalApplicationReturnBodyEvaluates.deterministic
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore leftStore rightStore : Core.Store} {body : Syntax.Block}
    {left right : Core.Value}
    (leftEvaluation : LocalApplicationReturnBodyEvaluates table environment initialStore body left leftStore)
    (rightEvaluation : LocalApplicationReturnBodyEvaluates table environment initialStore body right rightStore) :
    left = right ∧ leftStore = rightStore := by
  cases leftEvaluation with
  | application left =>
      cases rightEvaluation with
      | application right => exact left.deterministic right

theorem LocalApplicationReturnBodyEvaluatesWithCost.erase
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    LocalApplicationReturnBodyEvaluates table environment initialStore body value finalStore := by
  cases evaluation with
  | application child => exact .application child.erase

theorem LocalApplicationReturnBodyEvaluates.exists_cost
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : LocalApplicationReturnBodyEvaluates table environment initialStore body value finalStore) :
    ∃ cost, LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost := by
  cases evaluation with
  | application child =>
      obtain ⟨cost, counted⟩ := child.exists_cost
      exact ⟨cost, .application counted⟩

theorem localApplicationReturnBodyEvaluates_iff_exists_cost
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    LocalApplicationReturnBodyEvaluates table environment initialStore body value finalStore ↔
      ∃ cost, LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost :=
  ⟨LocalApplicationReturnBodyEvaluates.exists_cost, fun ⟨_, evaluation⟩ => evaluation.erase⟩

theorem LocalApplicationReturnBodyEvaluatesWithCost.deterministic
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore leftStore rightStore : Core.Store} {body : Syntax.Block}
    {left right : Core.Value} {leftCost rightCost : Nat}
    (leftEvaluation : LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore body left leftStore leftCost)
    (rightEvaluation : LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore body right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  cases leftEvaluation with
  | application left =>
      cases rightEvaluation with
      | application right => exact left.deterministic right

theorem LocalApplicationReturnBodyElaborates.evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationReturnBodyElaborates table context body core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalApplicationReturnBodyEvaluates table environment initialStore body value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  cases elaboration with
  | application child =>
      constructor
      · intro evaluation
        cases evaluation with
        | application actual => exact (child.evaluates_iff sameIds).mp actual
      · intro evaluation
        exact .application ((child.evaluates_iff sameIds).mpr evaluation)

/-- Keep the same actual cost before every continuation. Pending frames are
retained at the endpoint, not executed or assumed safe. -/
theorem LocalApplicationReturnBodyEvaluatesWithCost.toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationReturnBodyElaborates table context body core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  cases elaboration with
  | application child =>
      cases evaluation with
      | application actual => exact actual.toStepsWithContinuation child sameIds continuation

/-- Reflection compares exact costs only at a genuinely final closed endpoint. -/
theorem LocalApplicationReturnBodyElaborates.evaluatesWithCost_iff_steps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationReturnBodyElaborates table context body core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost ↔
      Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
        (Core.State.final value finalStore) := by
  cases elaboration with
  | application child =>
      constructor
      · intro evaluation
        cases evaluation with
        | application actual => exact (child.evaluatesWithCost_iff_steps sameIds).mp actual
      · intro path
        exact .application ((child.evaluatesWithCost_iff_steps sameIds).mpr path)

end Solcore.Frontend
