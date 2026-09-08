import Solcore.Frontend.TerminalReturnTreeRunnerProperties
import Solcore.Frontend.ReturnBodyFuelBoundProperties

/-! A total source-only budget includes the larger recursive arm. This is an
upper bound, not a minimum fuel threshold or a substitute for whole checking. -/

set_option autoImplicit false

namespace Solcore.Frontend

def terminalReturnTreeFuelBound (body : Syntax.Block) : Nat :=
  match body with
  | ⟨_, [⟨_, .returnStmt _⟩]⟩ => returnBodyFuelBound body
  | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ =>
      localExpressionFuelBound condition +
        max (terminalReturnTreeFuelBound thenBody) (terminalReturnTreeFuelBound elseBody) + 2
  | _ => 0
termination_by sizeOf body

/-- Raw selected-path costs are bounded even when a written unselected subtree
is unsupported. The numerical bound alone supplies no acceptance evidence. -/
theorem TerminalReturnTreeEvaluatesWithCost.cost_le_fuelBound
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost) :
    cost ≤ terminalReturnTreeFuelBound body := by
  induction evaluation with
  | single child =>
      have bounded := child.cost_le_fuelBound
      cases child <;> simpa only [terminalReturnTreeFuelBound] using bounded
  | ifTrue condition _ ih | ifFalse condition _ ih =>
      have conditionBound := condition.cost_le_fuelBound
      simp only [terminalReturnTreeFuelBound]
      omega

theorem elaborateTerminalReturnTree?_run_done_of_fuelBound
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) (fuel : Nat) (enough : terminalReturnTreeFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  obtain ⟨value, evaluated, valueTyped⟩ :=
    (elaborateTerminalReturnTree?_sound accepted).evaluates sameIds environmentTyped store
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  exact ⟨value, valueTyped, (costed.checked_runStateful_done_iff accepted sameIds).mpr
    (Nat.le_trans costed.cost_le_fuelBound enough)⟩

theorem LocalInputs.runTerminalReturnTree?_done_of_fuelBound
    {inputs : LocalInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : TerminalReturnTreeHasType inputs.names inputs.context body type)
    (store : Core.Store) (fuel : Nat) (enough : terminalReturnTreeFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧
      inputs.runTerminalReturnTree? fuel body store = some (type, .done value store) := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ := inputs.terminalReturnTree_typed_cost_execution typing store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

end Solcore.Frontend
