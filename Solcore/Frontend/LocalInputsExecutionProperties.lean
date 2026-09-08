import Solcore.Frontend.LocalInputsExecution
import Solcore.Frontend.LocalInputsProperties
import Solcore.Frontend.LocalExpressionExecutionProperties

/-! Typed input projection discharges runtime identity alignment automatically.
Whole-expression typing remains essential to the checked evaluation boundary. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem check?_iff_hasType {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty} :
    (∃ core, inputs.check? source = some (core, type)) ↔
      LocalExpressionHasType inputs.names inputs.context source type :=
  localExpressionHasType_iff_elaborates.symm

theorem run?_eq_some_iff {inputs : LocalInputs} {source : Syntax.Expr} {fuel : Nat}
    {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult} :
    inputs.run? fuel source store = some (type, result) ↔
      ∃ core, inputs.check? source = some (core, type) ∧
        Core.runStateful fuel
          (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store) = result := by
  simp only [run?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨⟨core, actualType⟩, checked, same⟩
    cases same
    exact ⟨core, checked, rfl⟩
  · rintro ⟨core, checked, resultEq⟩
    exact ⟨(core, type), checked, by simp only [resultEq]⟩

/-- Absence is independent of fuel: it means no checked Core was produced. -/
theorem run?_eq_none_iff {inputs : LocalInputs} {source : Syntax.Expr} (fuel : Nat)
    (store : Core.Store) : inputs.run? fuel source store = none ↔ inputs.check? source = none := by
  cases checked : inputs.check? source with
  | none => simp [run?, checked]
  | some pair => cases pair; simp [run?, checked]

theorem run?_done_sound {inputs : LocalInputs} {source : Syntax.Expr} {fuel : Nat}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value}
    (result : inputs.run? fuel source initialStore = some (type, .done value finalStore)) :
    LocalExpressionEvaluates inputs.names inputs.environment initialStore source value finalStore ∧
      Core.ValueHasType value type ∧ finalStore = initialStore := by
  obtain ⟨core, checked, execution⟩ := run?_eq_some_iff.mp result
  obtain ⟨evaluation, storeEq⟩ := elaborateLocalExpression?_run_done_sound
    checked inputs.sameIds execution
  have typing := check?_iff_hasType.mp ⟨core, checked⟩
  exact ⟨evaluation, (evaluation.preserves_type typing inputs.sameIds inputs.environmentTyped).1, storeEq⟩

theorem typed_run_has_sufficient_fuel {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalExpressionHasType inputs.names inputs.context source type) (store : Core.Store) :
    ∃ value required, LocalExpressionEvaluates inputs.names inputs.environment store source value store ∧
      Core.ValueHasType value type ∧
      ∀ fuel, required ≤ fuel → inputs.run? fuel source store = some (type, .done value store) := by
  obtain ⟨core, checked⟩ := check?_iff_hasType.mpr typing
  obtain ⟨value, required, evaluation, valueTyped, enough⟩ :=
    elaborateLocalExpression?_typed_execution checked inputs.sameIds inputs.environmentTyped store
  exact ⟨value, required, evaluation, valueTyped, fun fuel bounded =>
    run?_eq_some_iff.mpr ⟨core, checked, enough fuel bounded⟩⟩

/-- The exact executable completion boundary includes source typing. Raw
selected-branch evaluation alone does not imply whole-expression checking. -/
theorem run?_done_iff_typed_evaluation {inputs : LocalInputs} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} :
    (∃ fuel, inputs.run? fuel source initialStore = some (type, .done value finalStore)) ↔
      LocalExpressionHasType inputs.names inputs.context source type ∧
      LocalExpressionEvaluates inputs.names inputs.environment initialStore source value finalStore := by
  constructor
  · rintro ⟨fuel, result⟩
    obtain ⟨core, checked, _⟩ := run?_eq_some_iff.mp result
    exact ⟨check?_iff_hasType.mp ⟨core, checked⟩, (run?_done_sound result).1⟩
  · rintro ⟨typing, evaluation⟩
    obtain ⟨core, checked⟩ := check?_iff_hasType.mpr typing
    obtain ⟨fuel, execution⟩ := (elaborateLocalExpression?_evaluates_iff_run_done
      checked inputs.sameIds).mp evaluation
    exact ⟨fuel, run?_eq_some_iff.mpr ⟨core, checked, execution⟩⟩

/-- Any source either fails this checker or runs its typed pure Core. Even
at insufficient fuel, the convenience endpoint cannot return a machine fault. -/
theorem run?_never_faults (inputs : LocalInputs) (source : Syntax.Expr) (fuel : Nat)
    (store : Core.Store) (type : Core.Ty) (error : Core.MachineFault) (faultState : Core.State) :
    inputs.run? fuel source store ≠ some (type, .fault error faultState) := by
  intro result
  obtain ⟨core, checked, fault⟩ := run?_eq_some_iff.mp result
  exact elaborateLocalExpression?_run_never_faults checked inputs.sameIds inputs.environmentTyped
    store fuel error faultState fault

end Solcore.Frontend.LocalInputs
