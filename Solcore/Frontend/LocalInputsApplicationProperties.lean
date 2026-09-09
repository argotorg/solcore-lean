import Solcore.Frontend.LocalInputsApplication
import Solcore.Frontend.LocalInputsProperties
import Solcore.Frontend.LocalFunctionApplicationExecutionProperties

/-! The separate endpoint preserves its exact checked Core and every machine
result. Completion corresponds to whole typing plus independent source
evaluation; structural input typing alone adds no runtime value or store claim. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem checkApplication?_iff_elaborates {inputs : LocalInputs} {source : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty} :
    inputs.checkApplication? source = some (core, type) ↔
      LocalFunctionApplicationElaborates inputs.names inputs.context source core type :=
  elaborateLocalFunctionApplication?_iff

theorem checkApplication?_iff_hasType {inputs : LocalInputs} {source : Syntax.Expr}
    {type : Core.Ty} :
    (∃ core, inputs.checkApplication? source = some (core, type)) ↔
      LocalFunctionApplicationHasType inputs.names inputs.context source type := by
  constructor
  · rintro ⟨core, accepted⟩
    exact (checkApplication?_iff_elaborates.mp accepted).hasType
  · intro typing
    obtain ⟨core, elaboration⟩ := typing.elaborates_exact
    exact ⟨core, checkApplication?_iff_elaborates.mpr elaboration⟩

theorem runApplication?_eq_some_iff {inputs : LocalInputs} {source : Syntax.Expr}
    {fuel : Nat} {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult} :
    inputs.runApplication? fuel source store = some (type, result) ↔
      ∃ core, inputs.checkApplication? source = some (core, type) ∧
        Core.runStateful fuel
          (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store) = result := by
  simp only [runApplication?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨⟨core, actualType⟩, checked, same⟩
    cases same
    exact ⟨core, checked, rfl⟩
  · rintro ⟨core, checked, resultEq⟩
    exact ⟨(core, type), checked, by simp only [resultEq]⟩

/-- Only the static gate can produce outer absence, at every fuel and store. -/
theorem runApplication?_eq_none_iff {inputs : LocalInputs} {source : Syntax.Expr}
    (fuel : Nat) (store : Core.Store) :
    inputs.runApplication? fuel source store = none ↔ inputs.checkApplication? source = none := by
  cases checked : inputs.checkApplication? source with
  | none => simp [runApplication?, checked]
  | some pair => cases pair; simp [runApplication?, checked]

/-- An observed completion reflects source evaluation, not runtime typing of
the value or equality of the initial and final stores. -/
theorem runApplication?_done_sound {inputs : LocalInputs} {source : Syntax.Expr} {fuel : Nat}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value}
    (result : inputs.runApplication? fuel source initialStore = some (type, .done value finalStore)) :
    LocalFunctionApplicationEvaluates inputs.names inputs.environment
      initialStore source value finalStore := by
  obtain ⟨core, checked, execution⟩ := runApplication?_eq_some_iff.mp result
  exact ((checkApplication?_iff_elaborates.mp checked).evaluates_iff inputs.sameIds).mpr
    (Core.runStateful_evaluation_sound execution)

/-- Raw selected-path success alone does not establish the whole static gate.
Conversely, whole typing alone supplies no actual runtime-world validity. -/
theorem runApplication?_done_iff_typed_evaluation {inputs : LocalInputs} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} :
    (∃ fuel, inputs.runApplication? fuel source initialStore = some (type, .done value finalStore)) ↔
      LocalFunctionApplicationHasType inputs.names inputs.context source type ∧
      LocalFunctionApplicationEvaluates inputs.names inputs.environment
        initialStore source value finalStore := by
  constructor
  · rintro ⟨fuel, result⟩
    obtain ⟨core, checked, _⟩ := runApplication?_eq_some_iff.mp result
    exact ⟨checkApplication?_iff_hasType.mp ⟨core, checked⟩, runApplication?_done_sound result⟩
  · rintro ⟨typing, evaluation⟩
    obtain ⟨core, elaboration⟩ := typing.elaborates_exact
    obtain ⟨fuel, execution⟩ := Core.evaluation_runStateful_complete
      ((elaboration.evaluates_iff inputs.sameIds).mp evaluation)
    exact ⟨fuel, runApplication?_eq_some_iff.mpr
      ⟨core, checkApplication?_iff_elaborates.mpr elaboration, execution⟩⟩

end Solcore.Frontend.LocalInputs
