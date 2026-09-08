import Solcore.Frontend.LocalExpressionFuelBound
import Solcore.Frontend.LocalExpressionCostExecutionProperties

/-! Whole checked source with aligned typed actual values completes at any
fuel above its structural bound. The bound alone does not grant acceptance. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateLocalExpression?_run_done_of_fuelBound
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) (fuel : Nat) (enough : localExpressionFuelBound source ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧
      Core.runStateful fuel (Core.State.initial core
        (Resolved.LocalScope.values environment) store) = .done value store := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ :=
    elaborateLocalExpression?_typed_cost_execution accepted sameIds environmentTyped store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

theorem LocalInputs.run?_done_of_fuelBound
    {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalExpressionHasType inputs.names inputs.context source type)
    (store : Core.Store) (fuel : Nat) (enough : localExpressionFuelBound source ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ inputs.run? fuel source store = some (type, .done value store) := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ := inputs.typed_cost_execution typing store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

end Solcore.Frontend
