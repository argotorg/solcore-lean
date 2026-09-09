import Solcore.Frontend.LocalFunctionApplicationExecutionProperties
import Solcore.Core.Safety

/-! Runtime-world safety for the actual original call. Captures and referenced
locations share the supplied typed store. Structural value typing alone cannot
discharge these premises, and actual successful costs are not source bounds. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalFunctionApplicationEvaluates.preserves_runtime_type
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value}
    (evaluation : LocalFunctionApplicationEvaluates table environment initialStore source value finalStore)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {world : Core.StoreTyping}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world initialStore) :
    ∃ finalWorld, Core.WorldExtends world finalWorld ∧ Core.StoreHasTypes finalWorld finalStore ∧
      Core.RuntimeValueHasType finalWorld value type :=
  Core.evaluation_preserves_type ((elaboration.evaluates_iff sameIds).mp evaluation)
    elaboration.core_hasType environmentTyped storeTyped

/-- Whole source typing supplies successful evaluation only together with the
actual aligned environment and store typed in the same runtime world. -/
theorem LocalFunctionApplicationHasType.runtime_evaluates
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalFunctionApplicationHasType table context source type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world store) :
    ∃ finalWorld finalStore value cost, Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧ Core.RuntimeValueHasType finalWorld value type ∧
      LocalFunctionApplicationEvaluatesWithCost table environment store source value finalStore cost := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  have definitionsWellFormed : Core.DataEnvironment.WellFormed [] := by
    intro definition member
    cases member
  obtain ⟨finalWorld, finalStore, value, extension, finalTyped, evaluated, valueTyped⟩ :=
    Core.well_typed_evaluates elaboration.core_hasType definitionsWellFormed environmentTyped storeTyped
  obtain ⟨cost, exactEvaluation⟩ := ((elaboration.evaluates_iff sameIds).mpr evaluated).exists_cost
  exact ⟨finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, exactEvaluation⟩

/-- One actual successful cost gives all continuation-local paths and both
closed fuel thresholds. No completion claim is made for untyped pending frames. -/
theorem LocalFunctionApplicationElaborates.runtime_typed_execution
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world store) :
    ∃ finalWorld finalStore value cost, Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧ Core.RuntimeValueHasType finalWorld value type ∧
      LocalFunctionApplicationEvaluatesWithCost table environment store source value finalStore cost ∧
      (∀ continuation : List Core.Frame, Core.Steps cost
        ⟨.eval core (Resolved.LocalScope.values environment), continuation, store⟩
        ⟨.ret value, continuation, finalStore⟩) ∧
      ∀ fuel, (Core.runStateful fuel
        (Core.State.initial core (Resolved.LocalScope.values environment) store) =
          .done value finalStore ↔ cost ≤ fuel) ∧
        ((∃ checkpoint, Core.runStateful fuel
          (Core.State.initial core (Resolved.LocalScope.values environment) store) =
            .outOfFuel checkpoint) ↔ fuel < cost) := by
  obtain ⟨finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, evaluation⟩ :=
    elaboration.hasType.runtime_evaluates sameIds environmentTyped storeTyped
  have path := evaluation.toSteps elaboration sameIds
  exact ⟨finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, evaluation,
    evaluation.toStepsWithContinuation elaboration sameIds,
    fun _ => ⟨path.runStateful_done_iff, path.runStateful_outOfFuel_iff⟩⟩

theorem elaborateLocalFunctionApplication?_runtime_run_done_sound
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalFunctionApplication? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {world : Core.StoreTyping} {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world initialStore)
    (completed : Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) initialStore) =
        .done value finalStore) :
    LocalFunctionApplicationEvaluates table environment initialStore source value finalStore ∧
      ∃ finalWorld, Core.WorldExtends world finalWorld ∧ Core.StoreHasTypes finalWorld finalStore ∧
        Core.RuntimeValueHasType finalWorld value type := by
  have elaboration := elaborateLocalFunctionApplication?_sound accepted
  have evaluation := (elaboration.evaluates_iff sameIds).mpr (Core.runStateful_evaluation_sound completed)
  exact ⟨evaluation, evaluation.preserves_runtime_type elaboration sameIds environmentTyped storeTyped⟩

end Solcore.Frontend
