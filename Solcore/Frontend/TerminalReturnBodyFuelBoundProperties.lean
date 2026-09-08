import Solcore.Frontend.TerminalReturnBodyRunnerProperties
import Solcore.Frontend.ConditionalReturnBodyFuelBoundProperties

/-! Shape dispatch preserves the component source bound without extra cost.
An unsupported shape still receives zero and must pass checking before running. -/

set_option autoImplicit false

namespace Solcore.Frontend

def terminalReturnBodyFuelBound (body : Syntax.Block) : Nat :=
  match body.value with
  | [⟨_, .returnStmt _⟩] => returnBodyFuelBound body
  | [⟨_, .ifThen _ _ (some _)⟩] => conditionalReturnBodyFuelBound body
  | _ => 0

theorem TerminalReturnBodyEvaluatesWithCost.cost_le_fuelBound
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    cost ≤ terminalReturnBodyFuelBound body := by
  cases evaluation with
  | single child =>
      have bounded := child.cost_le_fuelBound
      cases child <;> exact bounded
  | conditional child =>
      have bounded := child.cost_le_fuelBound
      cases child <;> exact bounded

theorem elaborateTerminalReturnBody?_run_done_of_fuelBound
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) (fuel : Nat) (enough : terminalReturnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  obtain ⟨value, evaluated, valueTyped⟩ :=
    (elaborateTerminalReturnBody?_sound accepted).evaluates sameIds environmentTyped store
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  exact ⟨value, valueTyped, (costed.checked_runStateful_done_iff accepted sameIds).mpr
    (Nat.le_trans costed.cost_le_fuelBound enough)⟩

theorem LocalInputs.runTerminalReturnBody?_done_of_fuelBound
    {inputs : LocalInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : TerminalReturnBodyHasType inputs.names inputs.context body type)
    (store : Core.Store) (fuel : Nat) (enough : terminalReturnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧
      inputs.runTerminalReturnBody? fuel body store = some (type, .done value store) := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ := inputs.terminalReturnBody_typed_cost_execution typing store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

end Solcore.Frontend
