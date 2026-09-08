import Solcore.Frontend.TerminalReturnTreeElaboration
import Solcore.Frontend.TerminalReturnTreeEvaluationProperties
import Solcore.Frontend.ReturnBodyContinuationProperties

/-! Whole checked trees correspond to their exact Core under aligned IDs.
Runtime typing is unnecessary for correspondence; pending continuations remain
intact at the exact-cost path endpoint rather than being executed or unwound. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTerminalReturnTree?_evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    TerminalReturnTreeEvaluates table environment initialStore body value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  have elaboration := elaborateTerminalReturnTree?_elaborates accepted
  clear accepted
  induction elaboration generalizing initialStore finalStore value with
  | single elaboration =>
      constructor
      · intro evaluation
        cases evaluation with
        | single child => exact (elaborateReturnBody?_evaluates_iff elaboration.complete sameIds).mp child
        | ifTrue _ _ => cases elaboration
        | ifFalse _ _ => cases elaboration
      · intro evaluation
        exact .single ((elaborateReturnBody?_evaluates_iff elaboration.complete sameIds).mpr evaluation)
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      have conditionAccepted := elaborateLocalExpression?_complete resolution lowered typing
      constructor
      · intro evaluation
        cases evaluation with
        | single child => cases child
        | ifTrue condition branch =>
            exact .ifTrue ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mp condition)
              ((thenIH (initialStore := _) (finalStore := _) (value := _)).mp branch)
        | ifFalse condition branch =>
            exact .ifFalse ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mp condition)
              ((elseIH (initialStore := _) (finalStore := _) (value := _)).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mpr condition)
              ((thenIH (initialStore := _) (finalStore := _) (value := _)).mpr branch)
        | ifFalse condition branch =>
            exact .ifFalse ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mpr condition)
              ((elseIH (initialStore := _) (finalStore := _) (value := _)).mpr branch)

theorem TerminalReturnTreeEvaluatesWithCost.checked_toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  induction evaluation generalizing core type continuation with
  | single child =>
      cases elaborateTerminalReturnTree?_elaborates accepted with
      | single elaboration => exact child.checked_toStepsWithContinuation elaboration.complete sameIds continuation
      | conditional _ _ _ _ _ => cases child
  | ifTrue condition _ branchIH =>
      cases elaborateTerminalReturnTree?_elaborates accepted with
      | single elaboration => cases elaboration
      | conditional resolution lowered _ thenElaboration _ =>
          have runtimeLowered := lowered
          rw [← sameIds] at runtimeLowered
          exact CostStepComposition.ifTrue (condition.toStepsWithContinuation resolution runtimeLowered _)
            (branchIH (core := _) (type := _) (continuation := continuation) thenElaboration.complete)
  | ifFalse condition _ branchIH =>
      cases elaborateTerminalReturnTree?_elaborates accepted with
      | single elaboration => cases elaboration
      | conditional resolution lowered _ _ elseElaboration =>
          have runtimeLowered := lowered
          rw [← sameIds] at runtimeLowered
          exact CostStepComposition.ifFalse (condition.toStepsWithContinuation resolution runtimeLowered _)
            (branchIH (core := _) (type := _) (continuation := continuation) elseElaboration.complete)

theorem TerminalReturnTreeEvaluatesWithCost.checked_toSteps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) :=
  evaluation.checked_toStepsWithContinuation accepted sameIds []

end Solcore.Frontend
