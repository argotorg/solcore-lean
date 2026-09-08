import Solcore.Frontend.LocalExpressionEvaluatorProperties
import Solcore.Frontend.LocalInputsCostInvariance

/-! Direct source results meet the existing checked machine only through whole
checking and actual identity alignment. Raw success alone supplies neither.
Retained-continuation paths end before the continuation executes. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateLocalExpressionWithCost?_checked_toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat} {core : Core.Expr} {type : Core.Ty}
    {store : Core.Store}
    (evaluated : evaluateLocalExpressionWithCost? table environment source = some (value, cost))
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : environment.ids = context.ids) (continuation : List Core.Frame) :
    Core.Steps cost ⟨.eval core environment.values, continuation, store⟩
      ⟨.ret value, continuation, store⟩ := by
  obtain ⟨resolved, resolution, lowered, _⟩ := elaborateLocalExpression?_sound accepted
  have runtimeLowered : Resolved.Lowers environment.ids resolved core := by rw [sameIds]; exact lowered
  exact (evaluateLocalExpressionWithCost?_sound evaluated store).toStepsWithContinuation resolution runtimeLowered continuation

theorem evaluateLocalExpressionWithCost?_checked_runStateful_done_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {value : Core.Value} {cost fuel : Nat} {core : Core.Expr} {type : Core.Ty}
    {store : Core.Store}
    (evaluated : evaluateLocalExpressionWithCost? table environment source = some (value, cost))
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : environment.ids = context.ids) :
    Core.runStateful fuel (Core.State.initial core environment.values store) = .done value store ↔ cost ≤ fuel :=
  (evaluateLocalExpressionWithCost?_sound evaluated store).checked_runStateful_done_iff accepted sameIds

theorem evaluateLocalExpressionWithCost?_checked_runStateful_outOfFuel_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {value : Core.Value} {cost fuel : Nat} {core : Core.Expr} {type : Core.Ty}
    {store : Core.Store}
    (evaluated : evaluateLocalExpressionWithCost? table environment source = some (value, cost))
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : environment.ids = context.ids) :
    (∃ checkpoint, Core.runStateful fuel (Core.State.initial core environment.values store) = .outOfFuel checkpoint) ↔ fuel < cost :=
  (evaluateLocalExpressionWithCost?_sound evaluated store).checked_runStateful_outOfFuel_iff accepted sameIds

/-- Completion reflection retains the final store explicitly and needs no runtime
typing. Its checked lowering must still agree with the actual identity order. -/
theorem elaborateLocalExpression?_run_done_iff_evaluator
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : environment.ids = context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    Core.runStateful fuel (Core.State.initial core environment.values initialStore) = .done value finalStore ↔
      finalStore = initialStore ∧ ∃ cost, evaluateLocalExpressionWithCost? table environment source = some (value, cost) ∧ cost ≤ fuel := by
  rw [elaborateLocalExpression?_run_done_iff_cost accepted sameIds]
  constructor
  · rintro ⟨cost, evaluated, enough⟩
    exact ⟨evaluated.store_eq, cost, evaluateLocalExpressionWithCost?_complete evaluated, enough⟩
  · rintro ⟨rfl, cost, evaluated, enough⟩
    exact ⟨cost, evaluateLocalExpressionWithCost?_sound evaluated _, enough⟩

theorem elaborateLocalExpression?_typed_evaluator_exists
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : environment.ids = context.ids)
    (environmentTyped : Core.EnvironmentHasTypes environment.values context.values) :
    ∃ value cost, evaluateLocalExpressionWithCost? table environment source = some (value, cost) ∧ Core.ValueHasType value type := by
  obtain ⟨value, cost, evaluated, typed, _⟩ := elaborateLocalExpression?_typed_cost_execution accepted sameIds environmentTyped []
  exact ⟨value, cost, evaluateLocalExpressionWithCost?_complete evaluated, typed⟩

namespace LocalInputs

/-- The original whole-typing conjunct cannot be replaced by raw success. -/
theorem run?_done_iff_evaluator {inputs : LocalInputs} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    inputs.run? fuel source initialStore = some (type, .done value finalStore) ↔
      LocalExpressionHasType inputs.names inputs.context source type ∧ finalStore = initialStore ∧
      ∃ cost, evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (value, cost) ∧ cost ≤ fuel := by
  rw [run?_done_iff_typed_cost]
  constructor
  · rintro ⟨typing, cost, evaluated, enough⟩
    exact ⟨typing, evaluated.store_eq, cost, evaluateLocalExpressionWithCost?_complete evaluated, enough⟩
  · rintro ⟨typing, rfl, cost, evaluated, enough⟩
    exact ⟨typing, cost, evaluateLocalExpressionWithCost?_sound evaluated _, enough⟩

theorem run?_outOfFuel_iff_evaluator {inputs : LocalInputs} {source : Syntax.Expr}
    {store : Core.Store} {type : Core.Ty} {fuel : Nat} :
    (∃ checkpoint, inputs.run? fuel source store = some (type, .outOfFuel checkpoint)) ↔
      LocalExpressionHasType inputs.names inputs.context source type ∧
      ∃ value cost, evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (value, cost) ∧ fuel < cost := by
  rw [run?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨typing, value, cost, evaluated, short⟩
    exact ⟨typing, value, cost, evaluateLocalExpressionWithCost?_complete evaluated, short⟩
  · rintro ⟨typing, value, cost, evaluated, short⟩
    exact ⟨typing, value, cost, evaluateLocalExpressionWithCost?_sound evaluated store, short⟩

theorem typed_evaluator_execution {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalExpressionHasType inputs.names inputs.context source type) (store : Core.Store) :
    ∃ value cost, evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (value, cost) ∧
      Core.ValueHasType value type ∧ ∀ fuel,
        (inputs.run? fuel source store = some (type, .done value store) ↔ cost ≤ fuel) ∧
        ((∃ checkpoint, inputs.run? fuel source store = some (type, .outOfFuel checkpoint)) ↔ fuel < cost) := by
  obtain ⟨value, cost, evaluated, typed, boundaries⟩ := typed_cost_execution typing store
  exact ⟨value, cost, evaluateLocalExpressionWithCost?_complete evaluated, typed, boundaries⟩

end LocalInputs
end Solcore.Frontend
