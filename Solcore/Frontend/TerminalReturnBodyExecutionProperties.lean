import Solcore.Frontend.TerminalReturnBodyProperties
import Solcore.Frontend.TerminalReturnBodyEvaluationProperties
import Solcore.Frontend.ConditionalReturnBodyExecutionProperties

/-! The terminal wrapper preserves the exact component Core and all runtime
endpoints. The independent elaboration selects a disjoint source shape. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTerminalReturnBody?_evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    TerminalReturnBodyEvaluates table environment initialStore body value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  cases elaborateTerminalReturnBody?_elaborates accepted with
  | single elaboration =>
      constructor
      · intro evaluation
        cases evaluation with
        | single child => exact (elaborateReturnBody?_evaluates_iff elaboration.complete sameIds).mp child
        | conditional child => cases elaboration <;> cases child
      · intro evaluation
        exact .single ((elaborateReturnBody?_evaluates_iff elaboration.complete sameIds).mpr evaluation)
  | conditional elaboration =>
      constructor
      · intro evaluation
        cases evaluation with
        | single child => cases child <;> cases elaboration
        | conditional child => exact (elaborateConditionalReturnBody?_evaluates_iff elaboration.complete sameIds).mp child
      · intro evaluation
        exact .conditional ((elaborateConditionalReturnBody?_evaluates_iff elaboration.complete sameIds).mpr evaluation)

theorem TerminalReturnBodyEvaluatesWithCost.checked_toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  cases evaluation with
  | single child =>
      cases elaborateTerminalReturnBody?_elaborates accepted with
      | single elaboration => exact child.checked_toStepsWithContinuation elaboration.complete sameIds continuation
      | conditional elaboration => cases child <;> cases elaboration
  | conditional child =>
      cases elaborateTerminalReturnBody?_elaborates accepted with
      | single elaboration => cases elaboration <;> cases child
      | conditional elaboration => exact child.checked_toStepsWithContinuation elaboration.complete sameIds continuation

theorem TerminalReturnBodyEvaluatesWithCost.checked_toSteps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) :=
  evaluation.checked_toStepsWithContinuation accepted sameIds []

theorem TerminalReturnBodyEvaluatesWithCost.checked_runStateful_done_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.runStateful fuel (Core.State.initial core (Resolved.LocalScope.values environment) initialStore) =
      .done value finalStore ↔ cost ≤ fuel :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_done_iff

theorem TerminalReturnBodyEvaluatesWithCost.checked_runStateful_outOfFuel_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    (∃ suspended, Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel suspended) ↔ fuel < cost :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_outOfFuel_iff

theorem elaborateTerminalReturnBody?_run_done_iff_cost
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .done value finalStore ↔
      ∃ cost, TerminalReturnBodyEvaluatesWithCost table environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    have evaluation := (elaborateTerminalReturnBody?_evaluates_iff accepted sameIds).mpr
      (Core.runStateful_evaluation_sound completed)
    obtain ⟨cost, costed⟩ := evaluation.exists_cost
    exact ⟨cost, costed, (costed.checked_runStateful_done_iff accepted sameIds).mp completed⟩
  · rintro ⟨cost, costed, enough⟩
    exact (costed.checked_runStateful_done_iff accepted sameIds).mpr enough

end Solcore.Frontend
