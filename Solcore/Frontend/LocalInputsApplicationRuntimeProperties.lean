import Solcore.Frontend.LocalInputsApplicationCostProperties
import Solcore.Frontend.LocalFunctionApplicationRuntimeSafetyProperties
import Solcore.Frontend.LocalFunctionApplicationRuntimeStateProperties

/-! Runtime-world guarantees for the same actual values and store consumed by
the separate application endpoint. Structural input records do not replace
these premises; all outcomes retain the checked static type tag. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem runApplication?_runtime_done_sound
    {inputs : LocalInputs} {source : Syntax.Expr} {fuel : Nat}
    {world : Core.StoreTyping} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values inputs.environment) (Resolved.LocalScope.values inputs.context))
    (storeTyped : Core.StoreHasTypes world initialStore)
    (result : inputs.runApplication? fuel source initialStore = some (type, .done value finalStore)) :
    LocalFunctionApplicationEvaluates inputs.names inputs.environment initialStore source value finalStore ∧
      ∃ finalWorld, Core.WorldExtends world finalWorld ∧ Core.StoreHasTypes finalWorld finalStore ∧
        Core.RuntimeValueHasType finalWorld value type := by
  obtain ⟨core, checked, execution⟩ := runApplication?_eq_some_iff.mp result
  exact elaborateLocalFunctionApplication?_runtime_run_done_sound checked inputs.sameIds
    environmentTyped storeTyped execution

/-- Actual runtime-world typing supplies successful evaluation and an exact
cost for these inputs. Both fuel thresholds retain the same value and store. -/
theorem runApplication?_runtime_has_exact_cost
    {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalFunctionApplicationHasType inputs.names inputs.context source type)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values inputs.environment) (Resolved.LocalScope.values inputs.context))
    (storeTyped : Core.StoreHasTypes world store) :
    ∃ finalWorld finalStore value cost, Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧ Core.RuntimeValueHasType finalWorld value type ∧
      LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment store source value finalStore cost ∧
      ∀ fuel, (inputs.runApplication? fuel source store = some (type, .done value finalStore) ↔ cost ≤ fuel) ∧
        ((∃ checkpoint, inputs.runApplication? fuel source store = some (type, .outOfFuel checkpoint)) ↔ fuel < cost) := by
  obtain ⟨finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, evaluation⟩ :=
    typing.runtime_evaluates inputs.sameIds environmentTyped storeTyped
  exact ⟨finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, evaluation,
    fun fuel => ⟨runApplication?_done_iff_of_cost typing evaluation (fuel := fuel),
      runApplication?_outOfFuel_iff_of_cost typing evaluation (fuel := fuel)⟩⟩

theorem runApplication?_runtime_never_faults
    {inputs : LocalInputs} {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values inputs.environment) (Resolved.LocalScope.values inputs.context))
    (storeTyped : Core.StoreHasTypes world store)
    (source : Syntax.Expr) (fuel : Nat) (type : Core.Ty)
    (error : Core.MachineFault) (faultState : Core.State) :
    inputs.runApplication? fuel source store ≠ some (type, .fault error faultState) := by
  intro result
  obtain ⟨core, checked, fault⟩ := runApplication?_eq_some_iff.mp result
  have elaboration := checkApplication?_iff_elaborates.mp checked
  exact elaboration.runtime_run_never_faults environmentTyped storeTyped
    (.nil : Core.ContinuationHasType world [] type type) fuel error faultState fault

end Solcore.Frontend.LocalInputs
