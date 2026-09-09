import Solcore.Frontend.LocalComputationReturnTreeExecutionProperties
import Solcore.Frontend.LocalComputationReturnTreeEvaluationProperties
import Solcore.Frontend.LocalComputationFragmentInsertionPaths

/-! Supplied actual costs compose through mixed statements. A hidden discard
slot preserves the complete tail path, including its effects and actual captures. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem insert_zero_path {expr : Core.Expr} (fragment : LocalComputationFragment expr)
    {environment : Core.Environment} {initialStore finalStore : Core.Store}
    {value : Core.Value} {cost : Nat}
    (path : Core.Steps cost (.initial expr environment initialStore) (.final value finalStore))
    (inserted : Core.Value) (continuation : List Core.Frame) :
    Core.Steps cost ⟨.eval (expr.weakenAt 0) (inserted :: environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  obtain ⟨commonCost, paths⟩ := fragment.insertion_paths [] environment inserted (Core.steps_from_initial_sound path)
  have sameCost := (path.final_unique (paths []).1).1
  exact sameCost.symm ▸ (paths continuation).2

theorem LocalComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : LocalComputationReturnTreeEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type)
    (sameIds : environment.ids = inputs.context.ids) (continuation : List Core.Frame) :
    Core.Steps cost ⟨.eval core environment.values, continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  induction elaboration generalizing environment initialStore finalStore value cost continuation with
  | bare => cases evaluation; exact .cons .unit .refl
  | expression child =>
      cases evaluation with
      | expression actual => exact actual.toStepsWithContinuation child sameIds continuation
  | block _ ih =>
      cases evaluation with
      | block actual => exact ih actual sameIds continuation
  | @binding inputs _ _ _ _ _ _ _ _ _ _ _ _ child _ ih =>
      cases evaluation with
      | binding initializer tail =>
          rename_i middleStore boundValue initializerCost tailCost
          apply CostStepComposition.letE (initializer.toStepsWithContinuation child sameIds _)
          apply ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment)
          · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
          · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
              using congrArg (List.cons _) sameIds
  | @inferred inputs _ _ _ _ _ _ _ _ _ _ child _ ih =>
      cases evaluation with
      | inferred initializer tail =>
          rename_i middleStore boundValue initializerCost tailCost
          apply CostStepComposition.letE (initializer.toStepsWithContinuation child sameIds _)
          apply ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment)
          · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
          · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
              using congrArg (List.cons _) sameIds
  | discard child tailElaboration ih =>
      cases evaluation with
      | discard expression tail =>
          rename_i middleStore discardedValue expressionCost tailCost
          exact CostStepComposition.letE (expression.toStepsWithContinuation child sameIds _)
            (insert_zero_path tailElaboration.core_fragment (ih tail sameIds []) discardedValue continuation)
  | conditional guard _ _ thenIH elseIH =>
      cases evaluation with
      | ifTrue condition branch =>
          exact CostStepComposition.ifTrue (condition.toStepsWithContinuation guard sameIds _)
            (thenIH branch sameIds continuation)
      | ifFalse condition branch =>
          exact CostStepComposition.ifFalse (condition.toStepsWithContinuation guard sameIds _)
            (elseIH branch sameIds continuation)

theorem LocalComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type)
    (sameIds : environment.ids = inputs.context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    LocalComputationReturnTreeEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost ↔
      Core.Steps cost (.initial core environment.values initialStore) (.final value finalStore) := by
  constructor
  · intro evaluation
    exact evaluation.toStepsWithContinuation elaboration sameIds []
  · intro path
    have evaluation := (elaboration.evaluates_iff sameIds).mpr (Core.steps_from_initial_sound path)
    obtain ⟨actualCost, actual⟩ := localComputationReturnTreeEvaluates_iff_exists_cost.mp evaluation
    have sameCost := (path.final_unique (actual.toStepsWithContinuation elaboration sameIds [])).1
    exact sameCost.symm ▸ actual

end Solcore.Frontend
