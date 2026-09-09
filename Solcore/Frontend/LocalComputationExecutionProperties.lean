import Solcore.Frontend.LocalComputation
import Solcore.Frontend.LocalComputationEvaluationProperties
import Solcore.Frontend.LocalFunctionApplicationExecutionProperties

/-! Exact original child provenance connects both computation branches to Core.
Only runtime ID order is shared; actual values, effects and pending frames are
not inferred from structural types. Root calls cannot be pure expressions. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalComputationElaborates.evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalComputationEvaluates table environment initialStore source value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  cases elaboration with
  | pure resolution lowered _ =>
      rw [← sameIds] at lowered
      constructor
      · intro evaluation
        cases evaluation with
        | pure child => exact (resolution.core_evaluates_iff lowered).mp child
        | application child => cases child; cases resolution
      · intro evaluation
        exact .pure ((resolution.core_evaluates_iff lowered).mpr evaluation)
  | application child =>
      constructor
      · intro evaluation
        cases evaluation with
        | pure actual => cases child; cases actual
        | application actual => exact (child.evaluates_iff sameIds).mp actual
      · intro evaluation
        exact .application ((child.evaluates_iff sameIds).mpr evaluation)

/-- The supplied cost is fixed before the retained continuation. Its endpoint
need not be final, and any subsequent pending frames are not executed here. -/
theorem LocalComputationEvaluatesWithCost.toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : LocalComputationEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  cases elaboration with
  | pure resolution lowered _ =>
      rw [← sameIds] at lowered
      cases evaluation with
      | pure child => exact child.toStepsWithContinuation resolution lowered continuation
      | application child => cases child; cases resolution
  | application child =>
      cases evaluation with
      | pure actual => cases child; cases actual
      | application actual => exact actual.toStepsWithContinuation child sameIds continuation

theorem LocalComputationElaborates.evaluatesWithCost_iff_steps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    LocalComputationEvaluatesWithCost table environment
      initialStore source value finalStore cost ↔
      Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
        (Core.State.final value finalStore) := by
  constructor
  · intro evaluation
    exact evaluation.toStepsWithContinuation elaboration sameIds []
  · intro path
    have evaluation := (elaboration.evaluates_iff sameIds).mpr (Core.steps_from_initial_sound path)
    obtain ⟨actualCost, actual⟩ := localComputationEvaluates_iff_exists_cost.mp evaluation
    have sameCost := (path.final_unique (actual.toStepsWithContinuation elaboration sameIds [])).1
    exact sameCost.symm ▸ actual

end Solcore.Frontend
