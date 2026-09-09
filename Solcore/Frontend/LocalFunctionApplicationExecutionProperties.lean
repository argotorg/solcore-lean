import Solcore.Frontend.LocalFunctionApplicationProperties
import Solcore.Frontend.LocalFunctionApplicationEvaluationProperties
import Solcore.Frontend.LocalFunctionApplicationStepComposition
import Solcore.Frontend.LocalExpressionEvaluationProperties
import Solcore.Frontend.LocalExpressionCostCorrespondence

/-! Exact static provenance connects independent calls to the original Core
application. Ordered runtime IDs suffice; actual closure tags, captures, body
costs and final stores are not inferred from static context types. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalFunctionApplicationElaborates.evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalFunctionApplicationEvaluates table environment initialStore source value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  cases elaboration with
  | call functionResolution functionLowered _ argumentResolution argumentLowered _ =>
      rw [← sameIds] at functionLowered argumentLowered
      constructor
      · intro evaluation
        cases evaluation with
        | call functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply ((functionResolution.core_evaluates_iff functionLowered).mp functionEvaluation)
              ((argumentResolution.core_evaluates_iff argumentLowered).mp argumentEvaluation)
              bodyEvaluation
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .call ((functionResolution.core_evaluates_iff functionLowered).mpr functionEvaluation)
              ((argumentResolution.core_evaluates_iff argumentLowered).mpr argumentEvaluation)
              bodyEvaluation

/-- One supplied cost works for every continuation, including pending frames
that may fail after this endpoint. The actual body path remains unchanged. -/
theorem LocalFunctionApplicationEvaluatesWithCost.toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  cases elaboration with
  | call functionResolution functionLowered _ argumentResolution argumentLowered _ =>
      rw [← sameIds] at functionLowered argumentLowered
      cases evaluation with
      | call functionEvaluation argumentEvaluation bodyPath =>
          exact CostStepComposition.apply
            (functionEvaluation.toStepsWithContinuation functionResolution functionLowered _)
            (argumentEvaluation.toStepsWithContinuation argumentResolution argumentLowered _) bodyPath

theorem LocalFunctionApplicationEvaluatesWithCost.toSteps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) :=
  evaluation.toStepsWithContinuation elaboration sameIds []

theorem LocalFunctionApplicationElaborates.evaluatesWithCost_iff_steps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source value finalStore cost ↔
      Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
        (Core.State.final value finalStore) := by
  constructor
  · intro evaluation
    exact evaluation.toSteps elaboration sameIds
  · intro path
    have evaluation := (elaboration.evaluates_iff sameIds).mpr (Core.steps_from_initial_sound path)
    obtain ⟨actualCost, actual⟩ := evaluation.exists_cost
    have sameCost := (path.final_unique (actual.toSteps elaboration sameIds)).1
    exact sameCost.symm ▸ actual

/-- Cost is chosen before all continuations. Reflection uses the empty one,
whose return endpoint really is final; arbitrary endpoints need not be final. -/
theorem LocalFunctionApplicationElaborates.evaluates_iff_exists_uniform_steps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalFunctionApplicationEvaluates table environment initialStore source value finalStore ↔
      ∃ cost, ∀ continuation : List Core.Frame, Core.Steps cost
        ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ := by
  constructor
  · intro evaluation
    obtain ⟨cost, exactEvaluation⟩ := evaluation.exists_cost
    exact ⟨cost, exactEvaluation.toStepsWithContinuation elaboration sameIds⟩
  · rintro ⟨_, paths⟩
    exact (elaboration.evaluates_iff sameIds).mpr (Core.steps_from_initial_sound (paths []))

theorem elaborateLocalFunctionApplication?_evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalFunctionApplication? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalFunctionApplicationEvaluates table environment initialStore source value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore :=
  (elaborateLocalFunctionApplication?_sound accepted).evaluates_iff sameIds

theorem elaborateLocalFunctionApplication?_evaluatesWithCost_iff_steps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalFunctionApplication? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source value finalStore cost ↔
      Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
        (Core.State.final value finalStore) :=
  (elaborateLocalFunctionApplication?_sound accepted).evaluatesWithCost_iff_steps sameIds

end Solcore.Frontend
