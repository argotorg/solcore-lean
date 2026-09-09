import Solcore.Frontend.ComputationReturnTreeEvaluation
import Solcore.Frontend.ComputationReturnTreeFragmentProperties
import Solcore.Frontend.ComputationBodyFragmentInsertionProperties
import Solcore.Frontend.LocalTypeInputsProperties

/-! Whole-body Core correspondence uses separate child execution and insertion
laws at every original scope. Actual values and intermediate stores are retained. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ComputationReturnTreeElaborates.evaluates_iff
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}
    {F : Core.Expr → Prop}
    (childMembership : ∀ {table context source core type}, ChildElab table context source core type → F core)
    (childWeakening : ∀ {core}, F core → ∀ cutoff, F (core.weakenAt cutoff))
    (childInserts : ∀ {core}, F core → ∀ leading suffix inserted {initialStore finalStore value},
      Core.Evaluates (leading ++ inserted :: suffix) initialStore (core.weakenAt leading.length) value finalStore ↔
        Core.Evaluates (leading ++ suffix) initialStore core value finalStore)
    (childExecution : ∀ {table context environment source core type},
      ChildElab table context source core type → environment.ids = context.ids →
      ∀ {initialStore finalStore value}, ChildEval table environment initialStore source value finalStore ↔
        Core.Evaluates environment.values initialStore core value finalStore)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
    (sameIds : environment.ids = inputs.context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    ComputationReturnTreeEvaluates ChildEval owner inputs.names environment initialStore body value finalStore ↔
      Core.Evaluates environment.values initialStore core value finalStore := by
  induction elaboration generalizing environment initialStore finalStore value with
  | bare =>
      constructor <;> intro evaluation <;> cases evaluation <;> constructor
  | expression child =>
      constructor
      · intro evaluation
        cases evaluation with
        | expression evaluated => exact (childExecution child sameIds).mp evaluated
      · intro evaluation
        exact .expression ((childExecution child sameIds).mpr evaluation)
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
            refine .letE ((childExecution child sameIds).mp initializer) ?_
            apply (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mp
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
      · intro evaluation
        cases evaluation with
        | letE initializer tail =>
            rename_i bodyStore boundValue
            apply ComputationReturnTreeEvaluates.binding ((childExecution child sameIds).mpr initializer)
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
            refine .letE ((childExecution child sameIds).mp initializer) ?_
            apply (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mp
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
      · intro evaluation
        cases evaluation with
        | letE initializer tail =>
            rename_i bodyStore boundValue
            apply ComputationReturnTreeEvaluates.inferred ((childExecution child sameIds).mpr initializer)
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
            exact .letE ((childExecution child sameIds).mp head)
              ((ComputationBodyFragment.evaluates_insert_iff (F := F) childInserts
                (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening tailElaboration) [] environment.values discardedValue).mpr
                ((ih sameIds).mp tail))
      · intro evaluation
        cases evaluation with
        | letE head tail =>
            exact .discard ((childExecution child sameIds).mpr head)
              ((ih sameIds).mpr ((ComputationBodyFragment.evaluates_insert_iff (F := F) childInserts
                (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening tailElaboration) [] environment.values _).mp tail))
  | conditional guard _ _ thenIH elseIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((childExecution guard sameIds).mp condition) ((thenIH sameIds).mp branch)
        | ifFalse condition branch =>
            exact .ifFalse ((childExecution guard sameIds).mp condition) ((elseIH sameIds).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((childExecution guard sameIds).mpr condition) ((thenIH sameIds).mpr branch)
        | ifFalse condition branch =>
            exact .ifFalse ((childExecution guard sameIds).mpr condition) ((elseIH sameIds).mpr branch)

end Solcore.Frontend
