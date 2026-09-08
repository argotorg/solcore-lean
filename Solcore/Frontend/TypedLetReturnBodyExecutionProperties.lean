import Solcore.Frontend.TypedLetReturnBodyProperties
import Solcore.Frontend.TypedLetReturnBodyEvaluation
import Solcore.Frontend.TerminalReturnTreeExecutionProperties
import Solcore.Frontend.WordLessCostStepComposition

/-! Actual checked Core follows the original initializer and extended tail.
Aligned IDs suffice for correspondence, not for a runtime typing guarantee.
Exact paths retain arbitrary continuations without running those frames. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTypedLetReturnBody?_evaluates_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    TypedLetReturnBodyEvaluates owner inputs.names environment initialStore body value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  have elaboration := elaborateTypedLetReturnBody?_elaborates accepted
  clear accepted
  induction elaboration generalizing environment initialStore finalStore value with
  | terminal child =>
      constructor
      · intro evaluation
        cases evaluation with
        | terminal evaluated => exact (elaborateTerminalReturnTree?_evaluates_iff child.complete sameIds).mp evaluated
        | binding _ _ => cases child with | single returned => cases returned
      · intro evaluated
        exact .terminal ((elaborateTerminalReturnTree?_evaluates_iff child.complete sameIds).mpr evaluated)
  | @binding inputs _ _ name _ _ _ declaredType _ _ _ _ _ _ resolution lowered typing _ ih =>
      have initializerAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      constructor
      · intro evaluation
        cases evaluation with
        | terminal child => cases child with | single returned => cases returned
        | binding initializer tail =>
            rename_i middleStore boundValue
            refine .letE ((elaborateLocalExpression?_evaluates_iff initializerAccepted sameIds).mp initializer) ?_
            apply (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mp
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
      · intro evaluation
        cases evaluation with
        | letE initializer tail =>
            rename_i bodyStore boundValue
            apply TypedLetReturnBodyEvaluates.binding
              ((elaborateLocalExpression?_evaluates_iff initializerAccepted sameIds).mpr initializer)
            have tailEvaluation :=
              (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mpr tail
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tailEvaluation
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds

theorem TypedLetReturnBodyEvaluatesWithCost.checked_toStepsWithContinuation
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  have elaboration := elaborateTypedLetReturnBody?_elaborates accepted
  clear accepted
  induction elaboration generalizing environment initialStore finalStore value cost continuation with
  | terminal child =>
      cases evaluation with
      | terminal evaluated => exact evaluated.checked_toStepsWithContinuation child.complete sameIds continuation
      | binding _ _ => cases child with | single returned => cases returned
  | @binding inputs _ _ _ _ _ _ _ _ _ _ _ _ _ resolution lowered _ _ ih =>
      cases evaluation with
      | terminal child => cases child with | single returned => cases returned
      | binding initializer tail =>
          rename_i middleStore boundValue initializerCost tailCost
          have runtimeLowered := lowered
          rw [← LocalTypeInputs.context_ids, ← sameIds] at runtimeLowered
          apply CostStepComposition.letE (initializer.toStepsWithContinuation resolution runtimeLowered _)
          apply ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment)
          · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
          · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
              using congrArg (List.cons _) sameIds

theorem TypedLetReturnBodyEvaluatesWithCost.checked_toSteps
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context) :
    Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) :=
  evaluation.checked_toStepsWithContinuation accepted sameIds []

end Solcore.Frontend
