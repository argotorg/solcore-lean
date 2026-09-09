import Solcore.Frontend.TypedLetReturnTreeRunnerProperties
import Solcore.Frontend.ReturnBodyFuelBoundProperties

/-! The source-only budget adds strict initializer work and takes the larger
recursive arm. A positive budget neither supplies acceptance nor runtime values;
the selected cost can be smaller than this sufficient-fuel upper bound. -/

set_option autoImplicit false

namespace Solcore.Frontend

def typedLetReturnTreeFuelBound (body : Syntax.Block) : Nat :=
  match body with
  | ⟨_, [⟨_, .returnStmt _⟩]⟩ => returnBodyFuelBound body
  | ⟨blockSpan, ⟨_, .letDecl _ _ (some initializer)⟩ :: rest⟩ =>
      localExpressionFuelBound initializer + typedLetReturnTreeFuelBound ⟨blockSpan, rest⟩ + 2
  | ⟨blockSpan, ⟨_, .expression expression true⟩ :: rest⟩ =>
      localExpressionFuelBound expression + typedLetReturnTreeFuelBound ⟨blockSpan, rest⟩ + 2
  | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ =>
      localExpressionFuelBound condition +
        max (typedLetReturnTreeFuelBound thenBody) (typedLetReturnTreeFuelBound elseBody) + 2
  | _ => 0
termination_by sizeOf body

theorem TypedLetReturnTreeEvaluatesWithCost.cost_le_fuelBound
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    cost ≤ typedLetReturnTreeFuelBound body := by
  induction evaluation with
  | single child =>
      have bounded := child.cost_le_fuelBound
      cases child <;> simpa only [typedLetReturnTreeFuelBound] using bounded
  | binding initializer _ ih | inferred initializer _ ih | discard initializer _ ih =>
      have initializerBound := initializer.cost_le_fuelBound
      simp only [typedLetReturnTreeFuelBound]
      omega
  | ifTrue condition _ ih | ifFalse condition _ ih =>
      have conditionBound := condition.cost_le_fuelBound
      simp only [typedLetReturnTreeFuelBound]
      omega

theorem elaborateTypedLetReturnTree?_run_done_of_fuelBound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values inputs.context))
    (store : Core.Store) (fuel : Nat) (enough : typedLetReturnTreeFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  obtain ⟨value, evaluated, valueTyped⟩ :=
    (elaborateTypedLetReturnTree?_sound accepted).evaluates sameIds environmentTyped store
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  exact ⟨value, valueTyped, (costed.checked_runStateful_done_iff accepted sameIds).mpr
    (Nat.le_trans costed.cost_le_fuelBound enough)⟩

theorem LocalInputs.runTypedLetReturnTree?_done_of_fuelBound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnTreeHasType types owner inputs.toTypeInputs body type)
    (store : Core.Store) (fuel : Nat) (enough : typedLetReturnTreeFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧
      inputs.runTypedLetReturnTree? types owner fuel body store = some (type, .done value store) := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ :=
    inputs.typedLetReturnTree_typed_cost_execution typing store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

end Solcore.Frontend
