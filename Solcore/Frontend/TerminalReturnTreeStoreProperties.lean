import Solcore.Frontend.TerminalReturnTreeRunnerProperties
import Solcore.Frontend.ReturnBodyStoreProperties

/-! Independent selected paths replay at any store with identical values and
costs. Runner observations retain their own stores, not identical full states. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeEvaluates.change_store
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TerminalReturnTreeEvaluates table environment initialStore body value finalStore)
    (replacement : Core.Store) : TerminalReturnTreeEvaluates table environment replacement body value replacement := by
  induction evaluation with
  | single child => exact .single (child.change_store replacement)
  | ifTrue condition _ ih => exact .ifTrue (condition.change_store replacement) ih
  | ifFalse condition _ ih => exact .ifFalse (condition.change_store replacement) ih

theorem TerminalReturnTreeEvaluatesWithCost.change_store
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost)
    (replacement : Core.Store) : TerminalReturnTreeEvaluatesWithCost table environment replacement body value replacement cost := by
  induction evaluation with
  | single child => exact .single (child.change_store replacement)
  | ifTrue condition _ ih => exact .ifTrue (condition.change_store replacement) ih
  | ifFalse condition _ ih => exact .ifFalse (condition.change_store replacement) ih

theorem terminalReturnTreeEvaluates_store_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    TerminalReturnTreeEvaluates table environment initialStore body value finalStore ↔
      finalStore = initialStore ∧ TerminalReturnTreeEvaluates table environment replacement body value replacement := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

theorem terminalReturnTreeEvaluatesWithCost_store_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat} :
    TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost ↔
      finalStore = initialStore ∧
        TerminalReturnTreeEvaluatesWithCost table environment replacement body value replacement cost := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

/-- Each completed observation carries its own initial store. This is not an
equality of complete run results across different stores. -/
theorem LocalInputs.runTerminalReturnTree?_done_store_iff
    (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    inputs.runTerminalReturnTree? fuel body leftStore = some (type, .done value leftStore) ↔
      inputs.runTerminalReturnTree? fuel body rightStore = some (type, .done value rightStore) := by
  rw [LocalInputs.runTerminalReturnTree?_done_iff_typed_cost, LocalInputs.runTerminalReturnTree?_done_iff_typed_cost]
  constructor
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store rightStore, enough⟩
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store leftStore, enough⟩

/-- Only exhaustion presence is related; the actual checkpoints retain their
respective stores and are not identified with each other. -/
theorem LocalInputs.runTerminalReturnTree?_outOfFuel_store_iff
    (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) :
    (∃ checkpoint, inputs.runTerminalReturnTree? fuel body leftStore = some (type, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, inputs.runTerminalReturnTree? fuel body rightStore = some (type, .outOfFuel checkpoint) := by
  rw [LocalInputs.runTerminalReturnTree?_outOfFuel_iff_typed_cost, LocalInputs.runTerminalReturnTree?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store rightStore, short⟩
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store leftStore, short⟩

end Solcore.Frontend
