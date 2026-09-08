import Solcore.Frontend.TypedLetReturnBodyRunnerProperties
import Solcore.Frontend.TerminalReturnTreeFuelBoundProperties

/-! This total budget counts all initializer bounds and the terminal tree's
maximum-arm bound. Neither annotation meaning nor name freshness is a numerical
premise; the bound does not replace whole checking or actual typed values. -/

set_option autoImplicit false

namespace Solcore.Frontend

def typedLetReturnBodyFuelBound (body : Syntax.Block) : Nat :=
  match body with
  | ⟨blockSpan, ⟨_, .letDecl _ (some _) (some initializer)⟩ :: rest⟩ =>
      localExpressionFuelBound initializer + typedLetReturnBodyFuelBound ⟨blockSpan, rest⟩ + 2
  | _ => terminalReturnTreeFuelBound body
termination_by body.value.length

theorem TypedLetReturnBodyEvaluatesWithCost.cost_le_fuelBound
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    cost ≤ typedLetReturnBodyFuelBound body := by
  induction evaluation with
  | terminal child =>
      have bounded := child.cost_le_fuelBound
      cases child with
      | single returned => cases returned <;> simpa only [typedLetReturnBodyFuelBound] using bounded
      | ifTrue _ _ | ifFalse _ _ => simpa only [typedLetReturnBodyFuelBound] using bounded
  | binding initializer _ ih =>
      have initializerBound := initializer.cost_le_fuelBound
      simp only [typedLetReturnBodyFuelBound]
      omega

theorem elaborateTypedLetReturnBody?_run_done_of_fuelBound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values inputs.context))
    (store : Core.Store) (fuel : Nat) (enough : typedLetReturnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  obtain ⟨value, evaluated, valueTyped⟩ :=
    (elaborateTypedLetReturnBody?_sound accepted).evaluates sameIds environmentTyped store
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  exact ⟨value, valueTyped, (costed.checked_runStateful_done_iff accepted sameIds).mpr
    (Nat.le_trans costed.cost_le_fuelBound enough)⟩

theorem LocalInputs.runTypedLetReturnBody?_done_of_fuelBound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType types owner inputs.toTypeInputs body type)
    (store : Core.Store) (fuel : Nat) (enough : typedLetReturnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧
      inputs.runTypedLetReturnBody? types owner fuel body store = some (type, .done value store) := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ :=
    inputs.typedLetReturnBody_typed_cost_execution typing store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

end Solcore.Frontend
