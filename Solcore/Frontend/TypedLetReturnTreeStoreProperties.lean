import Solcore.Frontend.TypedLetReturnTreeRunnerProperties
import Solcore.Frontend.ReturnBodyStoreProperties

/-! Replay old-scope initializer values and selected recursive paths at any store.
Values and costs are fixed; completed and suspended observations retain their
own stores. This is not arbitrary-Core or pending-continuation store independence. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnTreeEvaluates.change_store
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore)
    (replacement : Core.Store) :
    TypedLetReturnTreeEvaluates owner table environment replacement body value replacement := by
  induction evaluation with
  | single child => exact .single (child.change_store replacement)
  | block _ ih => exact .block ih
  | binding initializer _ ih => exact .binding (initializer.change_store replacement) ih
  | inferred initializer _ ih => exact .inferred (initializer.change_store replacement) ih
  | discard expression _ ih => exact .discard (expression.change_store replacement) ih
  | ifTrue condition _ ih => exact .ifTrue (condition.change_store replacement) ih
  | ifFalse condition _ ih => exact .ifFalse (condition.change_store replacement) ih

theorem TypedLetReturnTreeEvaluatesWithCost.change_store
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost)
    (replacement : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner table environment replacement body value replacement cost := by
  induction evaluation with
  | single child => exact .single (child.change_store replacement)
  | block _ ih => exact .block ih
  | binding initializer _ ih => exact .binding (initializer.change_store replacement) ih
  | inferred initializer _ ih => exact .inferred (initializer.change_store replacement) ih
  | discard expression _ ih => exact .discard (expression.change_store replacement) ih
  | ifTrue condition _ ih => exact .ifTrue (condition.change_store replacement) ih
  | ifFalse condition _ ih => exact .ifFalse (condition.change_store replacement) ih

theorem typedLetReturnTreeEvaluates_store_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore ↔
      finalStore = initialStore ∧
        TypedLetReturnTreeEvaluates owner table environment replacement body value replacement := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

theorem typedLetReturnTreeEvaluatesWithCost_store_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat} :
    TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost ↔
      finalStore = initialStore ∧
        TypedLetReturnTreeEvaluatesWithCost owner table environment replacement body value replacement cost := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

/-- Equal values at the same fuel, each with its own store; not equality of
complete results across stores. Whole checking remains part of each run. -/
theorem LocalInputs.runTypedLetReturnTree?_done_store_iff
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    inputs.runTypedLetReturnTree? types owner fuel body leftStore = some (type, .done value leftStore) ↔
      inputs.runTypedLetReturnTree? types owner fuel body rightStore = some (type, .done value rightStore) := by
  rw [LocalInputs.runTypedLetReturnTree?_done_iff_typed_cost, LocalInputs.runTypedLetReturnTree?_done_iff_typed_cost]
  constructor
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store rightStore, enough⟩
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store leftStore, enough⟩

/-- Exhaustion presence agrees, but suspended states retain their distinct
stores and must be resumed separately without dropping pending let frames. -/
theorem LocalInputs.runTypedLetReturnTree?_outOfFuel_store_iff
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store) (type : Core.Ty) :
    (∃ checkpoint, inputs.runTypedLetReturnTree? types owner fuel body leftStore = some (type, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, inputs.runTypedLetReturnTree? types owner fuel body rightStore = some (type, .outOfFuel checkpoint) := by
  rw [LocalInputs.runTypedLetReturnTree?_outOfFuel_iff_typed_cost, LocalInputs.runTypedLetReturnTree?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store rightStore, short⟩
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store leftStore, short⟩

end Solcore.Frontend
