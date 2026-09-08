import Solcore.Frontend.ConditionalReturnBodyRunnerProperties
import Solcore.Frontend.ReturnBodyFuelBoundProperties

/-! A conservative bound includes the larger written return arm. Zero for an
unsupported whole shape does not certify acceptance or execution. -/

set_option autoImplicit false

namespace Solcore.Frontend

def conditionalReturnBodyFuelBound (body : Syntax.Block) : Nat :=
  match body.value with
  | [⟨_, .ifThen condition thenBody (some elseBody)⟩] =>
      localExpressionFuelBound condition + max (returnBodyFuelBound thenBody) (returnBodyFuelBound elseBody) + 2
  | _ => 0

theorem ConditionalReturnBodyEvaluatesWithCost.cost_le_fuelBound
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    cost ≤ conditionalReturnBodyFuelBound body := by
  cases evaluation with
  | ifTrue condition branch =>
      have conditionBound := condition.cost_le_fuelBound
      have branchBound := branch.cost_le_fuelBound
      simp only [conditionalReturnBodyFuelBound]
      omega
  | ifFalse condition branch =>
      have conditionBound := condition.cost_le_fuelBound
      have branchBound := branch.cost_le_fuelBound
      simp only [conditionalReturnBodyFuelBound]
      omega

theorem elaborateConditionalReturnBody?_run_done_of_fuelBound
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) (fuel : Nat) (enough : conditionalReturnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  obtain ⟨value, evaluated, valueTyped⟩ :=
    (elaborateConditionalReturnBody?_sound accepted).evaluates sameIds environmentTyped store
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  exact ⟨value, valueTyped, (costed.checked_runStateful_done_iff accepted sameIds).mpr
    (Nat.le_trans costed.cost_le_fuelBound enough)⟩

theorem LocalInputs.runConditionalReturnBody?_done_of_fuelBound
    {inputs : LocalInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : ConditionalReturnBodyHasType inputs.names inputs.context body type)
    (store : Core.Store) (fuel : Nat) (enough : conditionalReturnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧
      inputs.runConditionalReturnBody? fuel body store = some (type, .done value store) := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ := inputs.conditionalReturnBody_typed_cost_execution typing store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

end Solcore.Frontend
