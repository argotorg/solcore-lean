import Solcore.Frontend.TypedLetReturnTreeProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluationProperties
import Solcore.Frontend.ReturnBodyContinuationProperties
import Solcore.Frontend.WordLessCostStepComposition
import Solcore.Frontend.LocalFragmentProperties
import Solcore.Core.LocalFragmentExactInsertionProperties

/-! Whole checked trees follow old-scope initializers and the selected arm.
Aligned IDs suffice for correspondence, without runtime typing. Exact-cost
paths retain the original continuation without executing its pending frames. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTypedLetReturnTree?_evaluates_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    TypedLetReturnTreeEvaluates owner inputs.names environment initialStore body value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  have elaboration := elaborateTypedLetReturnTree?_elaborates accepted
  clear accepted
  induction elaboration generalizing environment initialStore finalStore value with
  | single child =>
      constructor
      · intro evaluation
        cases evaluation with
        | single evaluated => exact (elaborateReturnBody?_evaluates_iff child.complete sameIds).mp evaluated
        | block _ => cases child
        | binding _ _ => cases child
        | inferred _ _ => cases child
        | discard _ _ => cases child
        | ifTrue _ _ => cases child
        | ifFalse _ _ => cases child
      · intro evaluated
        exact .single ((elaborateReturnBody?_evaluates_iff child.complete sameIds).mpr evaluated)
  | block _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | single child => cases child
        | block evaluated => exact (ih sameIds).mp evaluated
      · intro evaluated
        exact .block ((ih sameIds).mpr evaluated)
  | @binding inputs _ _ name _ _ _ declaredType _ _ _ _ _ _ resolution lowered typing _ ih =>
      have initializerAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      constructor
      · intro evaluation
        cases evaluation with
        | single child => cases child
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
            apply TypedLetReturnTreeEvaluates.binding
              ((elaborateLocalExpression?_evaluates_iff initializerAccepted sameIds).mpr initializer)
            have tailEvaluation :=
              (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mpr tail
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tailEvaluation
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
  | @inferred inputs _ _ name _ _ inferredType _ _ _ _ _ resolution lowered typing _ ih =>
      have initializerAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      constructor
      · intro evaluation
        cases evaluation with
        | single child => cases child
        | inferred initializer tail =>
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
            apply TypedLetReturnTreeEvaluates.inferred
              ((elaborateLocalExpression?_evaluates_iff initializerAccepted sameIds).mpr initializer)
            have tailEvaluation :=
              (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mpr tail
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tailEvaluation
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
  | discard resolution lowered typing tailElaboration ih =>
      have expressionAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      constructor
      · intro evaluation
        cases evaluation with
        | single child => cases child
        | discard expression tail =>
            rename_i middleStore discardedValue
            exact .letE ((elaborateLocalExpression?_evaluates_iff expressionAccepted sameIds).mp expression)
              (((ih sameIds).mp tail).weakenAt_zero_localFragment tailElaboration.localFragment discardedValue)
      · intro evaluation
        cases evaluation with
        | letE expression tail =>
            exact .discard ((elaborateLocalExpression?_evaluates_iff expressionAccepted sameIds).mpr expression)
              ((ih sameIds).mpr (tail.reflect_weakenAt_zero_localFragment tailElaboration.localFragment))
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      have conditionAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      constructor
      · intro evaluation
        cases evaluation with
        | single child => cases child
        | ifTrue condition branch =>
            exact .ifTrue ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mp condition)
              ((thenIH sameIds).mp branch)
        | ifFalse condition branch =>
            exact .ifFalse ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mp condition)
              ((elseIH sameIds).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mpr condition)
              ((thenIH sameIds).mpr branch)
        | ifFalse condition branch =>
            exact .ifFalse ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mpr condition)
              ((elseIH sameIds).mpr branch)

theorem TypedLetReturnTreeEvaluatesWithCost.checked_toStepsWithContinuation
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  have elaboration := elaborateTypedLetReturnTree?_elaborates accepted
  clear accepted
  induction elaboration generalizing environment initialStore finalStore value cost continuation with
  | single child =>
      cases evaluation with
      | single evaluated => exact evaluated.checked_toStepsWithContinuation child.complete sameIds continuation
      | block _ => cases child
      | binding _ _ => cases child
      | inferred _ _ => cases child
      | discard _ _ => cases child
      | ifTrue _ _ => cases child
      | ifFalse _ _ => cases child
  | block _ ih =>
      cases evaluation with
      | single child => cases child
      | block evaluated => exact ih evaluated sameIds continuation
  | @binding inputs _ _ _ _ _ _ _ _ _ _ _ _ _ resolution lowered _ _ ih =>
      cases evaluation with
      | single child => cases child
      | binding initializer tail =>
          rename_i middleStore boundValue initializerCost tailCost
          have runtimeLowered := lowered
          rw [← LocalTypeInputs.context_ids, ← sameIds] at runtimeLowered
          apply CostStepComposition.letE (initializer.toStepsWithContinuation resolution runtimeLowered _)
          apply ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment)
          · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
          · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
              using congrArg (List.cons _) sameIds
  | @inferred inputs _ _ _ _ _ _ _ _ _ _ _ resolution lowered _ _ ih =>
      cases evaluation with
      | single child => cases child
      | inferred initializer tail =>
          rename_i middleStore boundValue initializerCost tailCost
          have runtimeLowered := lowered
          rw [← LocalTypeInputs.context_ids, ← sameIds] at runtimeLowered
          apply CostStepComposition.letE (initializer.toStepsWithContinuation resolution runtimeLowered _)
          apply ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment)
          · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
          · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
              using congrArg (List.cons _) sameIds
  | discard resolution lowered _ tailElaboration ih =>
      cases evaluation with
      | single child => cases child
      | discard expression tail =>
          rename_i middleStore discardedValue expressionCost tailCost
          have runtimeLowered := lowered
          rw [← LocalTypeInputs.context_ids, ← sameIds] at runtimeLowered
          have tailPath := ih tail sameIds []
          exact CostStepComposition.letE (expression.toStepsWithContinuation resolution runtimeLowered _)
            (tailPath.weakenAt_zero_localFragment tailElaboration.localFragment discardedValue continuation)
  | conditional resolution lowered _ _ _ thenIH elseIH =>
      have runtimeLowered := lowered
      rw [← LocalTypeInputs.context_ids, ← sameIds] at runtimeLowered
      cases evaluation with
      | single child => cases child
      | ifTrue condition branch =>
          exact CostStepComposition.ifTrue (condition.toStepsWithContinuation resolution runtimeLowered _)
            (thenIH branch sameIds continuation)
      | ifFalse condition branch =>
          exact CostStepComposition.ifFalse (condition.toStepsWithContinuation resolution runtimeLowered _)
            (elseIH branch sameIds continuation)

theorem TypedLetReturnTreeEvaluatesWithCost.checked_toSteps
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context) :
    Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) :=
  evaluation.checked_toStepsWithContinuation accepted sameIds []

end Solcore.Frontend
