import Solcore.Frontend.ReturnBodyExecutionProperties
import Solcore.Frontend.LocalExpressionStoreProperties

/-! Store replay preserves values and costs, while full states retain their
own stores. Completed observations and exhaustion presence are related. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ReturnBodyEvaluates.change_store
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : ReturnBodyEvaluates table environment initialStore body value finalStore)
    (replacement : Core.Store) : ReturnBodyEvaluates table environment replacement body value replacement := by
  cases evaluation with
  | bare => exact .bare
  | expression child => exact .expression (child.change_store replacement)

theorem ReturnBodyEvaluatesWithCost.change_store
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    (replacement : Core.Store) : ReturnBodyEvaluatesWithCost table environment replacement body value replacement cost := by
  cases evaluation with
  | bare => exact .bare
  | expression child => exact .expression (child.change_store replacement)

theorem returnBodyEvaluates_store_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    ReturnBodyEvaluates table environment initialStore body value finalStore ↔
      finalStore = initialStore ∧ ReturnBodyEvaluates table environment replacement body value replacement := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

theorem returnBodyEvaluatesWithCost_store_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat} :
    ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost ↔
      finalStore = initialStore ∧
        ReturnBodyEvaluatesWithCost table environment replacement body value replacement cost := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

/-- Each completed observation carries its own initial store. This is not an
equality of complete run results across different stores. -/
theorem LocalInputs.runReturnBody?_done_store_iff
    (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    inputs.runReturnBody? fuel body leftStore = some (type, .done value leftStore) ↔
      inputs.runReturnBody? fuel body rightStore = some (type, .done value rightStore) := by
  rw [LocalInputs.runReturnBody?_done_iff_typed_cost, LocalInputs.runReturnBody?_done_iff_typed_cost]
  constructor
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store rightStore, enough⟩
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store leftStore, enough⟩

/-- Only exhaustion presence is related; the actual checkpoints retain their
respective stores and are not identified with each other. -/
theorem LocalInputs.runReturnBody?_outOfFuel_store_iff
    (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) :
    (∃ checkpoint, inputs.runReturnBody? fuel body leftStore = some (type, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, inputs.runReturnBody? fuel body rightStore = some (type, .outOfFuel checkpoint) := by
  rw [LocalInputs.runReturnBody?_outOfFuel_iff_typed_cost, LocalInputs.runReturnBody?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store rightStore, short⟩
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store leftStore, short⟩

end Solcore.Frontend
