import Solcore.Frontend.LocalExpressionCostCorrespondence
import Solcore.Frontend.LocalExpressionCostProperties
import Solcore.Frontend.LocalInputsExecutionProperties
import Solcore.Core.ExactFuelProperties

/-! Exact completion and exhaustion boundaries for independently costed source
evaluation. Checking remains explicit at executable frontend boundaries; raw
evaluation alone cannot discharge an unresolved or untypable skipped branch. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalExpressionEvaluatesWithCost.runStateful_done_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost fuel : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {resolved : Resolved.Expr} {core : Core.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core) :
    Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .done value finalStore ↔ cost ≤ fuel :=
  (evaluation.toSteps resolution lowered).runStateful_done_iff

theorem LocalExpressionEvaluatesWithCost.runStateful_outOfFuel_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost fuel : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {resolved : Resolved.Expr} {core : Core.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core) :
    (∃ suspended, Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel suspended) ↔ fuel < cost :=
  (evaluation.toSteps resolution lowered).runStateful_outOfFuel_iff

theorem LocalExpressionEvaluatesWithCost.checked_toSteps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) := by
  obtain ⟨resolved, resolution, lowered, _⟩ := elaborateLocalExpression?_sound accepted
  have runtimeLowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core := by
    rw [sameIds]
    exact lowered
  exact evaluation.toSteps resolution runtimeLowered

theorem LocalExpressionEvaluatesWithCost.checked_runStateful_done_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost fuel : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .done value finalStore ↔ cost ≤ fuel :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_done_iff

theorem LocalExpressionEvaluatesWithCost.checked_runStateful_outOfFuel_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost fuel : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    (∃ suspended, Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel suspended) ↔ fuel < cost :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_outOfFuel_iff

/-- The supplied runtime environment need not be typed when reflecting an
actual completed run; its identity order must match the checked lowering. -/
theorem elaborateLocalExpression?_run_done_iff_cost
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .done value finalStore ↔
      ∃ cost, LocalExpressionEvaluatesWithCost table environment
        initialStore source value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨evaluation, _⟩ := elaborateLocalExpression?_run_done_sound accepted sameIds completed
    obtain ⟨cost, costed⟩ := evaluation.exists_cost
    exact ⟨cost, costed, (costed.checked_runStateful_done_iff accepted sameIds).mp completed⟩
  · rintro ⟨cost, costed, enough⟩
    exact (costed.checked_runStateful_done_iff accepted sameIds).mpr enough

/-- Typed aligned inputs supply a cost, a typed result, and both exact fuel
boundaries. No store-typing premise or additional terminal transition is used. -/
theorem elaborateLocalExpression?_typed_cost_execution
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) :
    ∃ value cost, LocalExpressionEvaluatesWithCost table environment store source value store cost ∧
      Core.ValueHasType value type ∧ ∀ fuel,
        (Core.runStateful fuel (Core.State.initial core
          (Resolved.LocalScope.values environment) store) = .done value store ↔ cost ≤ fuel) ∧
        ((∃ suspended, Core.runStateful fuel (Core.State.initial core
          (Resolved.LocalScope.values environment) store) = .outOfFuel suspended) ↔ fuel < cost) := by
  have typing := localExpressionHasType_iff_elaborates.mpr ⟨core, accepted⟩
  obtain ⟨value, evaluation, valueTyped⟩ := typing.evaluates sameIds environmentTyped store
  obtain ⟨cost, costed⟩ := evaluation.exists_cost
  exact ⟨value, cost, costed, valueTyped, fun _ =>
    ⟨costed.checked_runStateful_done_iff accepted sameIds,
      costed.checked_runStateful_outOfFuel_iff accepted sameIds⟩⟩

namespace LocalInputs

/-- Whole source typing is retained even when the supplied raw cost derivation
can skip an unresolved or untypable branch. -/
theorem run?_done_iff_typed_cost {inputs : LocalInputs} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    inputs.run? fuel source initialStore = some (type, .done value finalStore) ↔
      LocalExpressionHasType inputs.names inputs.context source type ∧
      ∃ cost, LocalExpressionEvaluatesWithCost inputs.names inputs.environment
        initialStore source value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨core, checked, execution⟩ := run?_eq_some_iff.mp completed
    exact ⟨check?_iff_hasType.mp ⟨core, checked⟩,
      (elaborateLocalExpression?_run_done_iff_cost checked inputs.sameIds).mp execution⟩
  · rintro ⟨typing, cost, costed, enough⟩
    obtain ⟨core, checked⟩ := check?_iff_hasType.mpr typing
    exact run?_eq_some_iff.mpr ⟨core, checked,
      (costed.checked_runStateful_done_iff checked inputs.sameIds).mpr enough⟩

theorem typed_cost_execution {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalExpressionHasType inputs.names inputs.context source type) (store : Core.Store) :
    ∃ value cost, LocalExpressionEvaluatesWithCost inputs.names inputs.environment
        store source value store cost ∧ Core.ValueHasType value type ∧ ∀ fuel,
      (inputs.run? fuel source store = some (type, .done value store) ↔ cost ≤ fuel) ∧
      ((∃ suspended, inputs.run? fuel source store = some (type, .outOfFuel suspended)) ↔ fuel < cost) := by
  obtain ⟨core, checked⟩ := check?_iff_hasType.mpr typing
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ :=
    elaborateLocalExpression?_typed_cost_execution checked inputs.sameIds inputs.environmentTyped store
  refine ⟨value, cost, costed, valueTyped, fun fuel => ?_⟩
  simpa only [run?, checked, bind, Option.bind_some, pure, Option.some.injEq,
    Prod.mk.injEq, true_and] using boundaries fuel

end LocalInputs
end Solcore.Frontend
