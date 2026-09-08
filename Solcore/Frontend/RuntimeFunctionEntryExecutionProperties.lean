import Solcore.Frontend.RuntimeFunctionEntryCost

/-! Exact fixed-fuel execution of independently prepared runtime entries.
Whole header, parameter, return-type, and exact-body preparation are retained;
no safety statement applies to arbitrary prepared records without provenance. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem runRuntimeFunction?_eq_some_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {fuel : Nat} {store : Core.Store}
    {type : Core.Ty} {result : Core.StatefulRunResult} :
    runRuntimeFunction? types owner declaration arguments fuel store = some (type, result) ↔
      ∃ prepared, RuntimeFunctionPrepares types owner declaration arguments prepared ∧
        prepared.returnType = type ∧ Core.runStateful fuel (Core.State.initial prepared.core
          (Resolved.LocalScope.values prepared.inputs.environment) store) = result := by
  simp only [runRuntimeFunction?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨prepared, accepted, same⟩
    cases same
    exact ⟨prepared, prepareRuntimeFunction?_iff.mp accepted, rfl, rfl⟩
  · rintro ⟨prepared, preparation, sameType, execution⟩
    exact ⟨prepared, preparation.complete, by simp only [sameType, execution]⟩

theorem RuntimeFunctionEvaluatesWithCost.run_done_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost fuel : Nat}
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost) :
    runRuntimeFunction? types owner declaration arguments fuel initialStore =
      some (type, .done value finalStore) ↔ cost ≤ fuel := by
  cases evaluation with
  | @intro prepared _ _ _ _ preparation bodyCost =>
      have boundary := bodyCost.checked_runStateful_done_iff preparation.body.complete
        prepared.inputs.sameIds (fuel := fuel)
      simpa only [runRuntimeFunction?, preparation.complete, bind, Option.bind_some, pure,
        Option.some.injEq, Prod.mk.injEq, true_and] using boundary

theorem RuntimeFunctionEvaluatesWithCost.run_outOfFuel_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost fuel : Nat}
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost) :
    (∃ suspended, runRuntimeFunction? types owner declaration arguments fuel initialStore =
      some (type, .outOfFuel suspended)) ↔ fuel < cost := by
  cases evaluation with
  | @intro prepared _ _ _ _ preparation bodyCost =>
      have boundary := bodyCost.checked_runStateful_outOfFuel_iff preparation.body.complete
        prepared.inputs.sameIds (fuel := fuel)
      simpa only [runRuntimeFunction?, preparation.complete, bind, Option.bind_some, pure,
        Option.some.injEq, Prod.mk.injEq, true_and] using boundary

/-- The source cost already contains the entire independent entry contract;
raw return-body cost alone does not imply entry acceptance. -/
theorem runRuntimeFunction?_done_iff_cost
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    runRuntimeFunction? types owner declaration arguments fuel initialStore =
      some (type, .done value finalStore) ↔
      ∃ cost, RuntimeFunctionEvaluatesWithCost types owner declaration arguments
        initialStore type value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨prepared, preparation, sameType, execution⟩ := runRuntimeFunction?_eq_some_iff.mp completed
    cases sameType
    obtain ⟨cost, bodyCost, enough⟩ :=
      (elaborateTerminalReturnTree?_run_done_iff_cost preparation.body.complete prepared.inputs.sameIds).mp execution
    exact ⟨cost, .intro preparation bodyCost, enough⟩
  · rintro ⟨cost, evaluation, enough⟩
    exact evaluation.run_done_iff.mpr enough

theorem runRuntimeFunction?_outOfFuel_iff_cost
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {store : Core.Store} {type : Core.Ty} {fuel : Nat} :
    (∃ suspended, runRuntimeFunction? types owner declaration arguments fuel store =
      some (type, .outOfFuel suspended)) ↔
      ∃ value cost, RuntimeFunctionEvaluatesWithCost types owner declaration arguments
        store type value store cost ∧ fuel < cost := by
  constructor
  · rintro ⟨suspended, exhausted⟩
    obtain ⟨prepared, preparation, sameType, execution⟩ := runRuntimeFunction?_eq_some_iff.mp exhausted
    cases sameType
    obtain ⟨value, evaluated, _⟩ := preparation.body.hasType.evaluates
      prepared.inputs.sameIds prepared.inputs.environmentTyped store
    obtain ⟨cost, bodyCost⟩ := evaluated.exists_cost
    exact ⟨value, cost, .intro preparation bodyCost,
      (bodyCost.checked_runStateful_outOfFuel_iff preparation.body.complete
        prepared.inputs.sameIds).mp ⟨suspended, execution⟩⟩
  · rintro ⟨value, cost, evaluation, short⟩
    exact evaluation.run_outOfFuel_iff.mpr short

/-- Whole entry typing supplies a typed result and both exact fuel boundaries.
Preparation itself contributes no Core transitions; the store is unchanged. -/
theorem RuntimeFunctionHasType.typed_cost_execution
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {type : Core.Ty}
    (typing : RuntimeFunctionHasType types owner declaration arguments type) (store : Core.Store) :
    ∃ value cost, RuntimeFunctionEvaluatesWithCost types owner declaration arguments
        store type value store cost ∧ Core.ValueHasType value type ∧ ∀ fuel,
      (runRuntimeFunction? types owner declaration arguments fuel store =
        some (type, .done value store) ↔ cost ≤ fuel) ∧
      ((∃ suspended, runRuntimeFunction? types owner declaration arguments fuel store =
        some (type, .outOfFuel suspended)) ↔ fuel < cost) := by
  obtain ⟨prepared, preparation, sameType⟩ := runtimeFunctionHasType_iff_prepares.mp typing
  cases sameType
  obtain ⟨value, evaluated, valueTyped⟩ := preparation.body.hasType.evaluates
    prepared.inputs.sameIds prepared.inputs.environmentTyped store
  obtain ⟨cost, bodyCost⟩ := evaluated.exists_cost
  have evaluation := RuntimeFunctionEvaluatesWithCost.intro preparation bodyCost
  exact ⟨value, cost, evaluation, valueTyped, fun _ =>
    ⟨evaluation.run_done_iff, evaluation.run_outOfFuel_iff⟩⟩

/-- The public entry rejects invalid preparation or executes its exact safe
Core. A hand-built prepared record alone is not a premise of this guarantee. -/
theorem runRuntimeFunction?_never_faults
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store)
    (type : Core.Ty) (error : Core.MachineFault) (faultState : Core.State) :
    runRuntimeFunction? types owner declaration arguments fuel store ≠
      some (type, .fault error faultState) := by
  intro fault
  obtain ⟨prepared, preparation, sameType, _⟩ := runRuntimeFunction?_eq_some_iff.mp fault
  cases sameType
  obtain ⟨value, cost, _, _, boundaries⟩ := preparation.hasType.typed_cost_execution store
  by_cases enough : cost ≤ fuel
  · have completed := (boundaries fuel).1.mpr enough
    rw [completed] at fault
    cases fault
  · obtain ⟨suspended, exhausted⟩ := (boundaries fuel).2.mpr (by omega)
    rw [exhausted] at fault
    cases fault

end Solcore.Frontend
