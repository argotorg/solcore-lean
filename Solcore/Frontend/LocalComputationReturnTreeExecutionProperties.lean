import Solcore.Frontend.LocalComputationReturnTreeEvaluation
import Solcore.Frontend.LocalComputationFragmentProperties
import Solcore.Frontend.LocalComputationFragmentInsertionProperties
import Solcore.Frontend.LocalComputationExecutionProperties
import Solcore.Frontend.LocalTypeInputsProperties

/-! Exact mixed-body correspondence needs the original ordered IDs, not typed
runtime values. Every strict child passes its actual store to its continuation. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalComputationReturnTreeElaborates.evaluates_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type)
    (sameIds : environment.ids = inputs.context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalComputationReturnTreeEvaluates owner inputs.names environment initialStore body value finalStore ↔
      Core.Evaluates environment.values initialStore core value finalStore := by
  induction elaboration generalizing environment initialStore finalStore value with
  | bare =>
      constructor <;> intro evaluation <;> cases evaluation <;> constructor
  | expression child =>
      constructor
      · intro evaluation
        cases evaluation with
        | expression evaluated => exact (child.evaluates_iff sameIds).mp evaluated
      · intro evaluation
        exact .expression ((child.evaluates_iff sameIds).mpr evaluation)
  | block _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | block evaluated => exact (ih sameIds).mp evaluated
      · intro evaluation
        exact .block ((ih sameIds).mpr evaluation)
  | @binding inputs _ _ name _ _ _ declaredType _ _ _ _ _ child _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | binding initializer tail =>
            rename_i middleStore boundValue
            refine .letE ((child.evaluates_iff sameIds).mp initializer) ?_
            apply (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mp
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
      · intro evaluation
        cases evaluation with
        | letE initializer tail =>
            rename_i bodyStore boundValue
            apply LocalComputationReturnTreeEvaluates.binding ((child.evaluates_iff sameIds).mpr initializer)
            have evaluated := (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mpr tail
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using evaluated
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
  | @inferred inputs _ _ name _ _ inferredType _ _ _ _ child _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | inferred initializer tail =>
            rename_i middleStore boundValue
            refine .letE ((child.evaluates_iff sameIds).mp initializer) ?_
            apply (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mp
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
      · intro evaluation
        cases evaluation with
        | letE initializer tail =>
            rename_i bodyStore boundValue
            apply LocalComputationReturnTreeEvaluates.inferred ((child.evaluates_iff sameIds).mpr initializer)
            have evaluated := (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mpr tail
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using evaluated
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
  | discard child tailElaboration ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | discard head tail =>
            rename_i middleStore discardedValue
            exact .letE ((child.evaluates_iff sameIds).mp head)
              ((tailElaboration.core_fragment.evaluates_insert_iff [] environment.values discardedValue).mpr
                ((ih sameIds).mp tail))
      · intro evaluation
        cases evaluation with
        | letE head tail =>
            exact .discard ((child.evaluates_iff sameIds).mpr head)
              ((ih sameIds).mpr ((tailElaboration.core_fragment.evaluates_insert_iff [] environment.values _).mp tail))
  | conditional guard _ _ thenIH elseIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((guard.evaluates_iff sameIds).mp condition) ((thenIH sameIds).mp branch)
        | ifFalse condition branch =>
            exact .ifFalse ((guard.evaluates_iff sameIds).mp condition) ((elseIH sameIds).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((guard.evaluates_iff sameIds).mpr condition) ((thenIH sameIds).mpr branch)
        | ifFalse condition branch =>
            exact .ifFalse ((guard.evaluates_iff sameIds).mpr condition) ((elseIH sameIds).mpr branch)

end Solcore.Frontend
