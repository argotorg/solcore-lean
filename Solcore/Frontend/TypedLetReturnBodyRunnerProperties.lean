import Solcore.Frontend.TypedLetReturnBodyRunner
import Solcore.Frontend.TypedLetReturnBodyExecutionProperties
import Solcore.Frontend.TypedLetReturnBodyEvaluationProperties

/-! Whole checking and independent costs determine exact fuel thresholds.
Actual typed inputs supply terminating paths without filling in static values. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnBodyEvaluatesWithCost.checked_runStateful_done_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner inputs.names environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) :
    Core.runStateful fuel (Core.State.initial core environment.values initialStore) = .done value finalStore ↔ cost ≤ fuel :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_done_iff

theorem TypedLetReturnBodyEvaluatesWithCost.checked_runStateful_outOfFuel_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner inputs.names environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) :
    (∃ suspended, Core.runStateful fuel (Core.State.initial core environment.values initialStore) =
      .outOfFuel suspended) ↔ fuel < cost :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_outOfFuel_iff

theorem elaborateTypedLetReturnBody?_run_done_iff_cost
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    Core.runStateful fuel (Core.State.initial core environment.values initialStore) = .done value finalStore ↔
      ∃ cost, TypedLetReturnBodyEvaluatesWithCost owner inputs.names environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    have evaluation := (elaborateTypedLetReturnBody?_evaluates_iff accepted sameIds).mpr
      (Core.runStateful_evaluation_sound completed)
    obtain ⟨cost, costed⟩ := evaluation.exists_cost
    exact ⟨cost, costed, (costed.checked_runStateful_done_iff accepted sameIds).mp completed⟩
  · rintro ⟨cost, costed, enough⟩
    exact (costed.checked_runStateful_done_iff accepted sameIds).mpr enough

namespace LocalInputs

private theorem aligned (inputs : LocalInputs) : inputs.environment.ids = inputs.toTypeInputs.context.ids := by
  simpa only [toTypeInputs_context] using inputs.sameIds

private theorem actualTypes (inputs : LocalInputs) :
    Core.EnvironmentHasTypes inputs.environment.values inputs.toTypeInputs.context.values := by
  simpa only [toTypeInputs_context] using inputs.environmentTyped

theorem runTypedLetReturnBody?_eq_none_iff
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {body : Syntax.Block} {fuel : Nat} {store : Core.Store} :
    inputs.runTypedLetReturnBody? types owner fuel body store = none ↔
      inputs.checkTypedLetReturnBody? types owner body = none := by
  cases checked : inputs.checkTypedLetReturnBody? types owner body with
  | none => simp [runTypedLetReturnBody?, checked]
  | some pair => rcases pair with ⟨core, type⟩; simp [runTypedLetReturnBody?, checked]

theorem runTypedLetReturnBody?_eq_some_iff
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {body : Syntax.Block} {fuel : Nat} {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult} :
    inputs.runTypedLetReturnBody? types owner fuel body store = some (type, result) ↔
      ∃ core, inputs.checkTypedLetReturnBody? types owner body = some (core, type) ∧
        Core.runStateful fuel (Core.State.initial core inputs.environment.values store) = result := by
  simp only [runTypedLetReturnBody?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨⟨core, actualType⟩, checked, same⟩
    cases same
    exact ⟨core, checked, rfl⟩
  · rintro ⟨core, checked, resultEq⟩
    exact ⟨(core, type), checked, by simp only [resultEq]⟩

theorem runTypedLetReturnBody?_done_iff_typed_cost
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    inputs.runTypedLetReturnBody? types owner fuel body initialStore = some (type, .done value finalStore) ↔
      TypedLetReturnBodyHasType types owner inputs.toTypeInputs body type ∧
      ∃ cost, TypedLetReturnBodyEvaluatesWithCost owner inputs.names inputs.environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨core, checked, execution⟩ := runTypedLetReturnBody?_eq_some_iff.mp completed
    refine ⟨elaborateTypedLetReturnBody?_sound checked, ?_⟩
    simpa only [toTypeInputs_names] using
      (elaborateTypedLetReturnBody?_run_done_iff_cost checked (aligned inputs)).mp execution
  · rintro ⟨typing, cost, costed, enough⟩
    obtain ⟨core, checked⟩ := typing.elaborates
    rw [← toTypeInputs_names inputs] at costed
    exact runTypedLetReturnBody?_eq_some_iff.mpr ⟨core, checked,
      (costed.checked_runStateful_done_iff checked (aligned inputs)).mpr enough⟩

/-- Values and exact thresholds come from actual typed inputs. A static type
or a raw path through rejected source is not sufficient for this wrapper. -/
theorem typedLetReturnBody_typed_cost_execution
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId} {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType types owner inputs.toTypeInputs body type) (store : Core.Store) :
    ∃ value cost, TypedLetReturnBodyEvaluatesWithCost owner inputs.names inputs.environment
        store body value store cost ∧ Core.ValueHasType value type ∧ ∀ fuel,
      (inputs.runTypedLetReturnBody? types owner fuel body store = some (type, .done value store) ↔ cost ≤ fuel) ∧
      ((∃ suspended, inputs.runTypedLetReturnBody? types owner fuel body store =
        some (type, .outOfFuel suspended)) ↔ fuel < cost) := by
  obtain ⟨core, checked⟩ := typing.elaborates
  obtain ⟨value, evaluated, valueTyped⟩ := typing.evaluates (aligned inputs) (actualTypes inputs) store
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  refine ⟨value, cost, by simpa only [toTypeInputs_names] using costed, valueTyped, fun fuel => ?_⟩
  have boundaries := And.intro (costed.checked_runStateful_done_iff checked (aligned inputs) (fuel := fuel))
    (costed.checked_runStateful_outOfFuel_iff checked (aligned inputs) (fuel := fuel))
  simpa only [runTypedLetReturnBody?, checkTypedLetReturnBody?, checked, bind, Option.bind_some, pure,
    Option.some.injEq, Prod.mk.injEq, true_and] using boundaries

theorem runTypedLetReturnBody?_outOfFuel_iff_typed_cost
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {store : Core.Store} {type : Core.Ty} {fuel : Nat} :
    (∃ suspended, inputs.runTypedLetReturnBody? types owner fuel body store = some (type, .outOfFuel suspended)) ↔
      TypedLetReturnBodyHasType types owner inputs.toTypeInputs body type ∧
      ∃ value cost, TypedLetReturnBodyEvaluatesWithCost owner inputs.names inputs.environment
        store body value store cost ∧ fuel < cost := by
  constructor
  · rintro ⟨suspended, exhausted⟩
    obtain ⟨core, checked, _⟩ := runTypedLetReturnBody?_eq_some_iff.mp exhausted
    have typing := elaborateTypedLetReturnBody?_sound checked
    obtain ⟨value, cost, costed, _, boundaries⟩ :=
      typedLetReturnBody_typed_cost_execution (inputs := inputs) typing store
    exact ⟨typing, value, cost, costed, (boundaries fuel).2.mp ⟨suspended, exhausted⟩⟩
  · rintro ⟨typing, value, cost, costed, short⟩
    obtain ⟨core, checked⟩ := typing.elaborates
    rw [← toTypeInputs_names inputs] at costed
    obtain ⟨suspended, exhausted⟩ :=
      (costed.checked_runStateful_outOfFuel_iff checked (aligned inputs)).mpr short
    exact ⟨suspended, runTypedLetReturnBody?_eq_some_iff.mpr ⟨core, checked, exhausted⟩⟩

theorem runTypedLetReturnBody?_never_faults (inputs : LocalInputs) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (body : Syntax.Block) (fuel : Nat) (store : Core.Store)
    (type : Core.Ty) (error : Core.MachineFault) (faultState : Core.State) :
    inputs.runTypedLetReturnBody? types owner fuel body store ≠ some (type, .fault error faultState) := by
  intro fault
  obtain ⟨core, checked, _⟩ := runTypedLetReturnBody?_eq_some_iff.mp fault
  have typing := elaborateTypedLetReturnBody?_sound checked
  obtain ⟨value, cost, _, _, boundaries⟩ :=
    typedLetReturnBody_typed_cost_execution (inputs := inputs) typing store
  by_cases enough : cost ≤ fuel
  · have completed := (boundaries fuel).1.mpr enough
    rw [completed] at fault
    cases fault
  · obtain ⟨suspended, exhausted⟩ := (boundaries fuel).2.mpr (by omega)
    rw [exhausted] at fault
    cases fault

end LocalInputs
end Solcore.Frontend
