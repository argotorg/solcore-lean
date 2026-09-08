import Solcore.Frontend.TerminalReturnTreeStoreProperties
import Solcore.Frontend.RuntimeFunctionCompiledExecutionProperties

/-! Store-independent values and exact costs lift through recursive-tree and
whole-entry contracts. Full results are not equated: each retains its own store. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeFunctionEvaluatesWithCost.change_store
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost : Nat}
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost) (replacement : Core.Store) :
    RuntimeFunctionEvaluatesWithCost types owner declaration arguments replacement type value replacement cost := by
  cases evaluation with
  | intro preparation body => exact .intro preparation (body.change_store replacement)

theorem runtimeFunctionEvaluatesWithCost_store_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore replacement : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost : Nat} :
    RuntimeFunctionEvaluatesWithCost types owner declaration arguments initialStore type value finalStore cost ↔
      finalStore = initialStore ∧ RuntimeFunctionEvaluatesWithCost types owner declaration arguments
        replacement type value replacement cost := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

/-- Values agree at the same fuel, but each completed result carries its own
initial store. This includes cases where preparation rejects on both sides. -/
theorem runRuntimeFunction?_done_store_iff
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (leftStore rightStore : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    runRuntimeFunction? types owner declaration arguments fuel leftStore = some (type, .done value leftStore) ↔
      runRuntimeFunction? types owner declaration arguments fuel rightStore = some (type, .done value rightStore) := by
  rw [runRuntimeFunction?_done_iff_cost, runRuntimeFunction?_done_iff_cost]
  constructor
  · rintro ⟨cost, evaluation, enough⟩
    exact ⟨cost, evaluation.change_store rightStore, enough⟩
  · rintro ⟨cost, evaluation, enough⟩
    exact ⟨cost, evaluation.change_store leftStore, enough⟩

/-- The corresponding suspended states are existential and are not equated. -/
theorem runRuntimeFunction?_outOfFuel_store_iff
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (leftStore rightStore : Core.Store) (type : Core.Ty) :
    (∃ suspended, runRuntimeFunction? types owner declaration arguments fuel leftStore =
      some (type, .outOfFuel suspended)) ↔
    (∃ suspended, runRuntimeFunction? types owner declaration arguments fuel rightStore =
      some (type, .outOfFuel suspended)) := by
  rw [runRuntimeFunction?_outOfFuel_iff_cost, runRuntimeFunction?_outOfFuel_iff_cost]
  constructor
  · rintro ⟨value, cost, evaluation, short⟩
    exact ⟨value, cost, evaluation.change_store rightStore, short⟩
  · rintro ⟨value, cost, evaluation, short⟩
    exact ⟨value, cost, evaluation.change_store leftStore, short⟩

theorem RuntimeFunctionCompiles.compiled_done_store_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {compiled : CompiledRuntimeFunction} (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = compiled.inputs.context.values.reverse)
    (fuel : Nat) (leftStore rightStore : Core.Store) (value : Core.Value) :
    Core.runStateful fuel (Core.State.initial compiled.core (arguments.reverse.map (·.value)) leftStore) =
      .done value leftStore ↔
    Core.runStateful fuel (Core.State.initial compiled.core (arguments.reverse.map (·.value)) rightStore) =
      .done value rightStore := by
  have same := runRuntimeFunction?_done_store_iff types owner declaration arguments fuel leftStore rightStore
    compiled.returnType value
  simpa only [compilation.run_eq arguments matchingTypes, Option.some.injEq, Prod.mk.injEq, true_and] using same

theorem RuntimeFunctionCompiles.compiled_outOfFuel_store_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {compiled : CompiledRuntimeFunction} (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = compiled.inputs.context.values.reverse)
    (fuel : Nat) (leftStore rightStore : Core.Store) :
    (∃ suspended, Core.runStateful fuel
      (Core.State.initial compiled.core (arguments.reverse.map (·.value)) leftStore) = .outOfFuel suspended) ↔
    (∃ suspended, Core.runStateful fuel
      (Core.State.initial compiled.core (arguments.reverse.map (·.value)) rightStore) = .outOfFuel suspended) := by
  have same := runRuntimeFunction?_outOfFuel_store_iff types owner declaration arguments fuel leftStore rightStore
    compiled.returnType
  simpa only [compilation.run_eq arguments matchingTypes, Option.some.injEq, Prod.mk.injEq, true_and] using same

end Solcore.Frontend
