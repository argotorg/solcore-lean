import Solcore.Frontend.TypedLetReturnBodyRunnerProperties
import Solcore.Frontend.TerminalReturnTreeStoreProperties

/-! Replay the original initializer values and exact costs at any store.
Completed observations and exhaustion presence retain their own stores. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnBodyEvaluates.change_store
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore)
    (replacement : Core.Store) :
    TypedLetReturnBodyEvaluates owner table environment replacement body value replacement := by
  induction evaluation with
  | terminal child => exact .terminal (child.change_store replacement)
  | binding initializer _ ih => exact .binding (initializer.change_store replacement) ih

theorem TypedLetReturnBodyEvaluatesWithCost.change_store
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost)
    (replacement : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner table environment replacement body value replacement cost := by
  induction evaluation with
  | terminal child => exact .terminal (child.change_store replacement)
  | binding initializer _ ih => exact .binding (initializer.change_store replacement) ih

theorem typedLetReturnBodyEvaluates_store_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore ↔
      finalStore = initialStore ∧
        TypedLetReturnBodyEvaluates owner table environment replacement body value replacement := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

theorem typedLetReturnBodyEvaluatesWithCost_store_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat} :
    TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost ↔
      finalStore = initialStore ∧
        TypedLetReturnBodyEvaluatesWithCost owner table environment replacement body value replacement cost := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

/-- Equal values at the same fuel, each with its own store; not equality of
complete results across stores. Whole checking remains part of each run. -/
theorem LocalInputs.runTypedLetReturnBody?_done_store_iff
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    inputs.runTypedLetReturnBody? types owner fuel body leftStore = some (type, .done value leftStore) ↔
      inputs.runTypedLetReturnBody? types owner fuel body rightStore = some (type, .done value rightStore) := by
  rw [LocalInputs.runTypedLetReturnBody?_done_iff_typed_cost, LocalInputs.runTypedLetReturnBody?_done_iff_typed_cost]
  constructor
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store rightStore, enough⟩
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store leftStore, enough⟩

/-- Exhaustion presence agrees, but suspended states retain their distinct
stores and must be resumed separately without dropping pending let frames. -/
theorem LocalInputs.runTypedLetReturnBody?_outOfFuel_store_iff
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store) (type : Core.Ty) :
    (∃ checkpoint, inputs.runTypedLetReturnBody? types owner fuel body leftStore = some (type, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, inputs.runTypedLetReturnBody? types owner fuel body rightStore = some (type, .outOfFuel checkpoint) := by
  rw [LocalInputs.runTypedLetReturnBody?_outOfFuel_iff_typed_cost, LocalInputs.runTypedLetReturnBody?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store rightStore, short⟩
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store leftStore, short⟩

end Solcore.Frontend
