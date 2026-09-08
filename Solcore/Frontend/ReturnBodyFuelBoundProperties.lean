import Solcore.Frontend.LocalExpressionFuelBoundProperties
import Solcore.Frontend.ReturnBodyExecutionProperties

/-! A singleton return inherits the source bound without wrapper transitions.
The zero placeholder for unsupported body shapes is not an acceptance claim. -/

set_option autoImplicit false

namespace Solcore.Frontend

def returnBodyFuelBound (body : Syntax.Block) : Nat :=
  match body.value with
  | [⟨_, .returnStmt none⟩] => 1
  | [⟨_, .returnStmt (some source)⟩] => localExpressionFuelBound source
  | _ => 0

theorem ReturnBodyEvaluatesWithCost.cost_le_fuelBound
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    cost ≤ returnBodyFuelBound body := by
  cases evaluation with
  | bare => exact Nat.le_refl _
  | expression child => exact child.cost_le_fuelBound

theorem elaborateReturnBody?_run_done_of_fuelBound
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) (fuel : Nat) (enough : returnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  obtain ⟨value, evaluated, valueTyped⟩ :=
    (elaborateReturnBody?_sound accepted).evaluates sameIds environmentTyped store
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  exact ⟨value, valueTyped, (costed.checked_runStateful_done_iff accepted sameIds).mpr
    (Nat.le_trans costed.cost_le_fuelBound enough)⟩

theorem LocalInputs.runReturnBody?_done_of_fuelBound
    {inputs : LocalInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : ReturnBodyHasType inputs.names inputs.context body type)
    (store : Core.Store) (fuel : Nat) (enough : returnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧
      inputs.runReturnBody? fuel body store = some (type, .done value store) := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ := inputs.returnBody_typed_cost_execution typing store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

end Solcore.Frontend
