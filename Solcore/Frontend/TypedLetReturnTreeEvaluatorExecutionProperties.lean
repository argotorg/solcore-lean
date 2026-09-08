import Solcore.Frontend.TypedLetReturnTreeEvaluatorProperties
import Solcore.Frontend.TypedLetReturnTreeRunnerProperties

/-! Whole checking and aligned actual IDs separately connect direct recursive
results to the checked machine. Raw success is not source acceptance, and a
retained-continuation path ends before its pending frames execute. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateTypedLetReturnTreeWithCost?_checked_toStepsWithContinuation
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {value : Core.Value}
    {cost : Nat} {core : Core.Expr} {type : Core.Ty} {store : Core.Store}
    (evaluated : evaluateTypedLetReturnTreeWithCost? owner inputs.names environment body = some (value, cost))
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) (continuation : List Core.Frame) :
    Core.Steps cost ⟨.eval core environment.values, continuation, store⟩
      ⟨.ret value, continuation, store⟩ :=
  (evaluateTypedLetReturnTreeWithCost?_sound evaluated store).checked_toStepsWithContinuation accepted sameIds continuation

theorem evaluateTypedLetReturnTreeWithCost?_checked_runStateful_done_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {value : Core.Value}
    {cost fuel : Nat} {core : Core.Expr} {type : Core.Ty} {store : Core.Store}
    (evaluated : evaluateTypedLetReturnTreeWithCost? owner inputs.names environment body = some (value, cost))
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) :
    Core.runStateful fuel (Core.State.initial core environment.values store) = .done value store ↔ cost ≤ fuel :=
  (evaluateTypedLetReturnTreeWithCost?_sound evaluated store).checked_runStateful_done_iff accepted sameIds

theorem evaluateTypedLetReturnTreeWithCost?_checked_runStateful_outOfFuel_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {value : Core.Value}
    {cost fuel : Nat} {core : Core.Expr} {type : Core.Ty} {store : Core.Store}
    (evaluated : evaluateTypedLetReturnTreeWithCost? owner inputs.names environment body = some (value, cost))
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) :
    (∃ checkpoint, Core.runStateful fuel (Core.State.initial core environment.values store) = .outOfFuel checkpoint) ↔ fuel < cost :=
  (evaluateTypedLetReturnTreeWithCost?_sound evaluated store).checked_runStateful_outOfFuel_iff accepted sameIds

/-- Final-store equality remains explicit even though the direct evaluator has
no store parameter. Known checked completion needs no runtime typing premise. -/
theorem elaborateTypedLetReturnTree?_run_done_iff_evaluator
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    Core.runStateful fuel (Core.State.initial core environment.values initialStore) = .done value finalStore ↔
      finalStore = initialStore ∧ ∃ cost,
        evaluateTypedLetReturnTreeWithCost? owner inputs.names environment body = some (value, cost) ∧ cost ≤ fuel := by
  rw [elaborateTypedLetReturnTree?_run_done_iff_cost accepted sameIds]
  constructor
  · rintro ⟨cost, evaluated, enough⟩
    exact ⟨evaluated.store_eq, cost, evaluateTypedLetReturnTreeWithCost?_complete evaluated, enough⟩
  · rintro ⟨rfl, cost, evaluated, enough⟩
    exact ⟨cost, evaluateTypedLetReturnTreeWithCost?_sound evaluated _, enough⟩

theorem elaborateTypedLetReturnTree?_typed_evaluator_exists
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids)
    (environmentTyped : Core.EnvironmentHasTypes environment.values inputs.context.values) :
    ∃ value cost, evaluateTypedLetReturnTreeWithCost? owner inputs.names environment body = some (value, cost) ∧
      Core.ValueHasType value type := by
  obtain ⟨value, evaluated, typed⟩ :=
    (elaborateTypedLetReturnTree?_sound accepted).evaluates sameIds environmentTyped []
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  exact ⟨value, cost, evaluateTypedLetReturnTreeWithCost?_complete costed, typed⟩

namespace LocalInputs

theorem runTypedLetReturnTree?_done_iff_evaluator
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    inputs.runTypedLetReturnTree? types owner fuel body initialStore = some (type, .done value finalStore) ↔
      TypedLetReturnTreeHasType types owner inputs.toTypeInputs body type ∧ finalStore = initialStore ∧
      ∃ cost, evaluateTypedLetReturnTreeWithCost? owner inputs.names inputs.environment body = some (value, cost) ∧ cost ≤ fuel := by
  rw [runTypedLetReturnTree?_done_iff_typed_cost]
  constructor
  · rintro ⟨typing, cost, evaluated, enough⟩
    exact ⟨typing, evaluated.store_eq, cost, evaluateTypedLetReturnTreeWithCost?_complete evaluated, enough⟩
  · rintro ⟨typing, rfl, cost, evaluated, enough⟩
    exact ⟨typing, cost, evaluateTypedLetReturnTreeWithCost?_sound evaluated _, enough⟩

theorem runTypedLetReturnTree?_outOfFuel_iff_evaluator
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {store : Core.Store} {type : Core.Ty} {fuel : Nat} :
    (∃ checkpoint, inputs.runTypedLetReturnTree? types owner fuel body store = some (type, .outOfFuel checkpoint)) ↔
      TypedLetReturnTreeHasType types owner inputs.toTypeInputs body type ∧
      ∃ value cost, evaluateTypedLetReturnTreeWithCost? owner inputs.names inputs.environment body = some (value, cost) ∧ fuel < cost := by
  rw [runTypedLetReturnTree?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨typing, value, cost, evaluated, short⟩
    exact ⟨typing, value, cost, evaluateTypedLetReturnTreeWithCost?_complete evaluated, short⟩
  · rintro ⟨typing, value, cost, evaluated, short⟩
    exact ⟨typing, value, cost, evaluateTypedLetReturnTreeWithCost?_sound evaluated store, short⟩

theorem typedLetReturnTree_evaluator_execution
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId} {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnTreeHasType types owner inputs.toTypeInputs body type) (store : Core.Store) :
    ∃ value cost, evaluateTypedLetReturnTreeWithCost? owner inputs.names inputs.environment body = some (value, cost) ∧
      Core.ValueHasType value type ∧ ∀ fuel,
        (inputs.runTypedLetReturnTree? types owner fuel body store = some (type, .done value store) ↔ cost ≤ fuel) ∧
        ((∃ checkpoint, inputs.runTypedLetReturnTree? types owner fuel body store = some (type, .outOfFuel checkpoint)) ↔ fuel < cost) := by
  obtain ⟨value, cost, evaluated, typed, boundaries⟩ := typedLetReturnTree_typed_cost_execution typing store
  exact ⟨value, cost, evaluateTypedLetReturnTreeWithCost?_complete evaluated, typed, boundaries⟩

end LocalInputs
end Solcore.Frontend
