import Solcore.Frontend.LocalExpressionTypingProperties
import Solcore.Frontend.LocalExpressionEvaluationProperties
import Solcore.Frontend.LocalExpressionSafetyProperties
import Solcore.Core.Correspondence

/-! Checked canonical local expressions execute in an identity-aligned runtime
environment. Fuel exhaustion does not invalidate the source typing judgment. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateLocalExpression?_evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalExpressionEvaluates table environment initialStore source value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  obtain ⟨resolved, resolution, lowered, _⟩ := elaborateLocalExpression?_sound accepted
  have environmentLowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core := by
    rw [sameIds]
    exact lowered
  exact resolution.core_evaluates_iff environmentLowered

theorem elaborateLocalExpression?_run_done_sound
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (result : Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) initialStore) =
        .done value finalStore) :
    LocalExpressionEvaluates table environment initialStore source value finalStore ∧
      finalStore = initialStore := by
  have evaluation := (elaborateLocalExpression?_evaluates_iff accepted sameIds).mpr
    (Core.runStateful_evaluation_sound result)
  exact ⟨evaluation, evaluation.store_eq⟩

theorem elaborateLocalExpression?_evaluates_iff_run_done
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalExpressionEvaluates table environment initialStore source value finalStore ↔
      ∃ fuel, Core.runStateful fuel
        (Core.State.initial core (Resolved.LocalScope.values environment) initialStore) =
          .done value finalStore := by
  constructor
  · intro evaluation
    obtain ⟨required, enough⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel
      ((elaborateLocalExpression?_evaluates_iff accepted sameIds).mp evaluation)
    exact ⟨required, enough required (Nat.le_refl _)⟩
  · rintro ⟨fuel, result⟩
    exact (elaborateLocalExpression?_run_done_sound accepted sameIds result).1

/-- Typed open local environments give existence, not only uniqueness, and
the exact source value is returned at every sufficiently large Core fuel. -/
theorem elaborateLocalExpression?_typed_execution
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) :
    ∃ value required, LocalExpressionEvaluates table environment store source value store ∧
      Core.ValueHasType value type ∧
      ∀ fuel, required ≤ fuel → Core.runStateful fuel
        (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  have typing := localExpressionHasType_iff_elaborates.mpr ⟨core, accepted⟩
  obtain ⟨value, evaluation, valueTyped⟩ := typing.evaluates sameIds environmentTyped store
  obtain ⟨required, enough⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel
    ((elaborateLocalExpression?_evaluates_iff accepted sameIds).mp evaluation)
  exact ⟨value, required, evaluation, valueTyped, enough⟩

/-- Insufficient fuel cannot produce a machine fault for this checked pure
fragment. No runtime store-typing premise is needed for returning local values. -/
theorem elaborateLocalExpression?_run_never_faults
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) (fuel : Nat) (error : Core.MachineFault) (faultState : Core.State) :
    Core.runStateful fuel (Core.State.initial core (Resolved.LocalScope.values environment) store) ≠
      .fault error faultState := by
  intro fault
  obtain ⟨value, required, _, _, enough⟩ :=
    elaborateLocalExpression?_typed_execution accepted sameIds environmentTyped store
  obtain ⟨steps, _, path, terminal⟩ := Core.runStateful_fault_sound fault
  have stillFault := Core.runStateful_fault_complete_of_steps path terminal
    (Nat.le_max_right required steps)
  have done := enough (max required steps) (Nat.le_max_left required steps)
  rw [done] at stillFault
  cases stillFault

end Solcore.Frontend
