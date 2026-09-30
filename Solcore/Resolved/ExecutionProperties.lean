import Solcore.Resolved.Typing
import Solcore.Resolved.Eval
import Solcore.Core.Safety

set_option autoImplicit false

namespace Solcore.Resolved

/-- A completed Core run reflects to the independent resolved evaluation. -/
theorem Lowers.run_done_sound
    {environment : Environment} {initialStore finalStore : Core.Store}
    {expr : Expr} {core : Core.Expr} {value : Core.Value} {fuel : Nat}
    (lowered : Lowers (LocalScope.ids environment) expr core)
    (result : Core.runStateful fuel
      (Core.State.initial core (LocalScope.values environment) initialStore) =
        .done value finalStore) :
    Evaluates environment initialStore expr value finalStore ∧ finalStore = initialStore := by
  have evaluation := Evaluates.ofCore lowered (Core.runStateful_evaluation_sound result)
  exact ⟨evaluation, evaluation.store_eq⟩

/-- Every independent evaluation of an elaboratable expression is executable. -/
theorem Evaluates.run_has_sufficient_fuel
    {environment : Environment} {initialStore finalStore : Core.Store}
    {expr : Expr} {core : Core.Expr} {value : Core.Value}
    (evaluation : Evaluates environment initialStore expr value finalStore)
    (lowered : Lowers (LocalScope.ids environment) expr core) :
    ∃ required, ∀ fuel, required ≤ fuel →
      Core.runStateful fuel
        (Core.State.initial core (LocalScope.values environment) initialStore) =
          .done value finalStore :=
  Core.evaluation_runStateful_complete_with_sufficient_fuel (evaluation.toCore lowered)

theorem Lowers.evaluates_iff_run_done
    {environment : Environment} {initialStore finalStore : Core.Store}
    {expr : Expr} {core : Core.Expr} {value : Core.Value}
    (lowered : Lowers (LocalScope.ids environment) expr core) :
    Evaluates environment initialStore expr value finalStore ↔
      ∃ fuel, Core.runStateful fuel
        (Core.State.initial core (LocalScope.values environment) initialStore) =
          .done value finalStore := by
  constructor
  · intro evaluation
    obtain ⟨required, enough⟩ := evaluation.run_has_sufficient_fuel lowered
    exact ⟨required, enough required (Nat.le_refl _)⟩
  · rintro ⟨fuel, result⟩
    exact (lowered.run_done_sound result).1

/-- Closed typing proves existence, not just uniqueness of possible results. -/
theorem HasType.closed_evaluates {expr : Expr} {type : Core.Ty}
    (typing : HasType [] expr type) :
    ∃ value, Evaluates [] [] expr value [] ∧ Core.ValueHasType value type := by
  obtain ⟨core, lowered, coreTyped⟩ := typing.lowers
  obtain ⟨value, coreEvaluation, valueTyped⟩ :=
    lowered.localFragment.runtime_evaluates coreTyped
      (Core.RuntimeEnvironmentHasTypes.nil (world := [])) []
  have evaluation := Evaluates.ofCore (environment := []) lowered coreEvaluation
  exact ⟨value, evaluation, valueTyped.erase⟩

/-- Typed closed expressions elaborate and return the same value at every
sufficient fuel. The store is unchanged; no numeric source-literal policy is assumed. -/
theorem HasType.closed_run_has_sufficient_fuel {expr : Expr} {type : Core.Ty}
    (typing : HasType [] expr type) :
    ∃ core value required,
      expr.lower? [] = some core ∧
      Evaluates [] [] expr value [] ∧ Core.ValueHasType value type ∧
      ∀ fuel, required ≤ fuel → Core.runStateful fuel (Core.State.initial core) =
        .done value [] := by
  obtain ⟨core, lowered, _⟩ := typing.lowers
  obtain ⟨value, evaluation, valueTyped⟩ := typing.closed_evaluates
  obtain ⟨required, enough⟩ := evaluation.run_has_sufficient_fuel lowered
  exact ⟨core, value, required, lowered.complete, evaluation, valueTyped, enough⟩

/-- Insufficient fuel cannot turn a well-typed closed lowering into a machine fault. -/
theorem Lowers.closed_run_never_faults {expr : Expr} {core : Core.Expr} {type : Core.Ty}
    (lowered : Lowers [] expr core) (typing : HasType [] expr type)
    (fuel : Nat) (error : Core.MachineFault) (faultState : Core.State) :
    Core.runStateful fuel (Core.State.initial core) ≠ .fault error faultState :=
  Core.well_typed_runStateful_never_faults
    (Core.initial_state_has_type (Lowers.preserves_type (context := []) lowered typing))

end Solcore.Resolved
