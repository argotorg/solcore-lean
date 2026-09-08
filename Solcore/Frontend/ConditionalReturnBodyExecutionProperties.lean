import Solcore.Frontend.ConditionalReturnBodyProperties
import Solcore.Frontend.ConditionalReturnBodyEvaluationProperties
import Solcore.Frontend.ReturnBodyContinuationProperties

/-! Exact checked simulation for terminal conditionals. Whole elaboration keeps
both arms; raw reflection needs identity alignment but no typed environment. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateConditionalReturnBody?_evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    ConditionalReturnBodyEvaluates table environment initialStore body value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  cases elaborateConditionalReturnBody?_elaborates accepted with
  | intro resolution lowered typing thenElaboration elseElaboration =>
      have conditionAccepted := elaborateLocalExpression?_complete resolution lowered typing
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mp condition)
              ((elaborateReturnBody?_evaluates_iff thenElaboration.complete sameIds).mp branch)
        | ifFalse condition branch =>
            exact .ifFalse ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mp condition)
              ((elaborateReturnBody?_evaluates_iff elseElaboration.complete sameIds).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mpr condition)
              ((elaborateReturnBody?_evaluates_iff thenElaboration.complete sameIds).mpr branch)
        | ifFalse condition branch =>
            exact .ifFalse ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mpr condition)
              ((elaborateReturnBody?_evaluates_iff elseElaboration.complete sameIds).mpr branch)

theorem ConditionalReturnBodyEvaluatesWithCost.checked_toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  cases elaborateConditionalReturnBody?_elaborates accepted with
  | intro resolution lowered _ thenElaboration elseElaboration =>
      have runtimeLowered := lowered
      rw [← sameIds] at runtimeLowered
      cases evaluation with
      | ifTrue condition branch =>
          exact CostStepComposition.ifTrue (condition.toStepsWithContinuation resolution runtimeLowered _)
            (branch.checked_toStepsWithContinuation thenElaboration.complete sameIds continuation)
      | ifFalse condition branch =>
          exact CostStepComposition.ifFalse (condition.toStepsWithContinuation resolution runtimeLowered _)
            (branch.checked_toStepsWithContinuation elseElaboration.complete sameIds continuation)

theorem ConditionalReturnBodyEvaluatesWithCost.checked_toSteps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) :=
  evaluation.checked_toStepsWithContinuation accepted sameIds []

theorem ConditionalReturnBodyEvaluatesWithCost.checked_runStateful_done_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.runStateful fuel (Core.State.initial core (Resolved.LocalScope.values environment) initialStore) =
      .done value finalStore ↔ cost ≤ fuel :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_done_iff

theorem ConditionalReturnBodyEvaluatesWithCost.checked_runStateful_outOfFuel_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    (∃ suspended, Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel suspended) ↔ fuel < cost :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_outOfFuel_iff

theorem elaborateConditionalReturnBody?_run_done_iff_cost
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .done value finalStore ↔
      ∃ cost, ConditionalReturnBodyEvaluatesWithCost table environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    have evaluation := (elaborateConditionalReturnBody?_evaluates_iff accepted sameIds).mpr
      (Core.runStateful_evaluation_sound completed)
    obtain ⟨cost, costed⟩ := evaluation.exists_cost
    exact ⟨cost, costed, (costed.checked_runStateful_done_iff accepted sameIds).mp completed⟩
  · rintro ⟨cost, costed, enough⟩
    exact (costed.checked_runStateful_done_iff accepted sameIds).mpr enough

end Solcore.Frontend
