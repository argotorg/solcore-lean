import Solcore.Frontend.SourceCoreDirectLinking
import Solcore.Core.Safety

/-! Small checked laws for the specialized direct-call linking boundary. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDirectLinking

@[simp] theorem LinkedProgram.findEntry?_empty (key : SpecializationKey) :
    ({ entries := [] : LinkedProgram }).findEntry? key = none := by
  rfl

theorem LinkedEntry.run?_of_matching_types (entry : LinkedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store)
    (finite : entry.runtime = none)
    (typesEqual : inputs.map Core.Value.type = entry.elaborated.inputs.values) :
    entry.run? inputs fuel store = some (Core.runStateful fuel
      (Core.State.initial entry.elaborated.core inputs store)) := by
  simp [LinkedEntry.run?, LinkedEntry.runExact?, finite, typesEqual]

theorem LinkedEntry.runExact?_of_matching_types (entry : LinkedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store)
    (finite : entry.runtime = none)
    (typesEqual : inputs.map Core.Value.type = entry.elaborated.inputs.values) :
    entry.runExact? inputs fuel store = some (.core (Core.runStateful fuel
      (Core.State.initial entry.elaborated.core inputs store))) := by
  simp [LinkedEntry.runExact?, finite, typesEqual]

theorem LinkedEntry.run?_of_mismatched_types (entry : LinkedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store)
    (mismatch : inputs.map Core.Value.type ≠
      entry.elaborated.inputs.values) :
    entry.run? inputs fuel store = none := by
  simp [LinkedEntry.run?, LinkedEntry.runExact?, mismatch]

theorem LinkedEntry.runExact?_of_mismatched_types (entry : LinkedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store)
    (mismatch : inputs.map Core.Value.type ≠
      entry.elaborated.inputs.values) :
    entry.runExact? inputs fuel store = none := by
  simp [LinkedEntry.runExact?, mismatch]

/-- A successful direct-Core entry preserves both its independently checked
result type and a well-typed store.  The runtime environment premise is
deliberately deep: the public tag check alone cannot justify closure or cell
contents supplied by a caller. -/
theorem LinkedEntry.runExact?_core_done_preserves_type
    (entry : LinkedEntry) (inputs : List Core.Value) (fuel : Nat)
    (store : Core.Store) {world : Core.StoreTyping}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world inputs
      entry.elaborated.inputs.values)
    (storeTyped : Core.StoreHasTypes world store)
    {value : Core.Value} {finalStore : Core.Store}
    (ran : entry.runExact? inputs fuel store =
      some (.core (.done value finalStore))) :
    ∃ finalWorld,
      Core.StoreHasTypes finalWorld finalStore ∧
      Core.RuntimeValueHasType finalWorld value
        entry.elaborated.returnType := by
  have typesEqual : inputs.map Core.Value.type =
      entry.elaborated.inputs.values :=
    environmentTyped.type_tags
  have coreRan : Core.runStateful fuel
      (Core.State.initial entry.elaborated.core inputs store) =
        .done value finalStore := by
    unfold LinkedEntry.runExact? at ran
    simp only [typesEqual, ↓reduceIte] at ran
    split at ran
    · simpa using ran
    · simp at ran
  have initialTyped : Core.StateHasType
      (Core.State.initial entry.elaborated.core inputs store)
      entry.elaborated.returnType :=
    .eval storeTyped environmentTyped
      (Core.infer_sound entry.elaborated.coreTypeChecked) .nil
  exact Core.well_typed_runStateful_preserves_result_type
    initialTyped coreRan

/-- Deeply typed caller values and store also exclude every Core machine fault
on the direct backend, at every finite fuel budget. -/
theorem LinkedEntry.runExact?_core_never_faults
    (entry : LinkedEntry) (inputs : List Core.Value) (fuel : Nat)
    (store : Core.Store) {world : Core.StoreTyping}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world inputs
      entry.elaborated.inputs.values)
    (storeTyped : Core.StoreHasTypes world store)
    (error : Core.MachineFault) (faultState : Core.State) :
    entry.runExact? inputs fuel store ≠
      some (.core (.fault error faultState)) := by
  have typesEqual : inputs.map Core.Value.type =
      entry.elaborated.inputs.values :=
    environmentTyped.type_tags
  have initialTyped : Core.StateHasType
      (Core.State.initial entry.elaborated.core inputs store)
      entry.elaborated.returnType :=
    .eval storeTyped environmentTyped
      (Core.infer_sound entry.elaborated.coreTypeChecked) .nil
  intro faulted
  have coreFaulted : Core.runStateful fuel
      (Core.State.initial entry.elaborated.core inputs store) =
        .fault error faultState := by
    unfold LinkedEntry.runExact? at faulted
    simp only [typesEqual, ↓reduceIte] at faulted
    split at faulted
    · simpa using faulted
    · simp at faulted
  exact Core.well_typed_runStateful_never_faults initialTyped coreFaulted

/-- The compatibility projection has the same preservation guarantee on the
finite direct-Core path. -/
theorem LinkedEntry.run?_core_done_preserves_type
    (entry : LinkedEntry) (inputs : List Core.Value) (fuel : Nat)
    (store : Core.Store) {world : Core.StoreTyping}
    (finite : entry.runtime = none)
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world inputs
      entry.elaborated.inputs.values)
    (storeTyped : Core.StoreHasTypes world store)
    {value : Core.Value} {finalStore : Core.Store}
    (ran : entry.run? inputs fuel store = some (.done value finalStore)) :
    ∃ finalWorld,
      Core.StoreHasTypes finalWorld finalStore ∧
      Core.RuntimeValueHasType finalWorld value
        entry.elaborated.returnType := by
  have typesEqual : inputs.map Core.Value.type =
      entry.elaborated.inputs.values :=
    environmentTyped.type_tags
  have coreRan : Core.runStateful fuel
      (Core.State.initial entry.elaborated.core inputs store) =
        .done value finalStore := by
    simpa [LinkedEntry.run?, LinkedEntry.runExact?, finite, typesEqual] using ran
  have initialTyped : Core.StateHasType
      (Core.State.initial entry.elaborated.core inputs store)
      entry.elaborated.returnType :=
    .eval storeTyped environmentTyped
      (Core.infer_sound entry.elaborated.coreTypeChecked) .nil
  exact Core.well_typed_runStateful_preserves_result_type
    initialTyped coreRan

@[simp] theorem link_budgetExhausted (program : CheckedProgram) (plan : Plan)
    (next : SpecializationKey)
    (pending : List SourceSpecializationWorklist.Request) :
    link program (.budgetExhausted plan next pending) =
      .error (.budgetExhausted next pending.length) := by
  rfl

@[simp] theorem linkWithStagingFuel_budgetExhausted
    (program : CheckedProgram) (plan : Plan) (next : SpecializationKey)
    (pending : List SourceSpecializationWorklist.Request) (fuel : Nat) :
    linkWithStagingFuel program (.budgetExhausted plan next pending) fuel =
      .error (.budgetExhausted next pending.length) := by
  rfl

@[simp] theorem link_eq_linkWithStagingFuel_default
    (program : CheckedProgram)
    (outcome : SourceSpecializationWorklist.Outcome) :
    link program outcome = linkWithStagingFuel program outcome 1024 := by
  rfl

end Solcore.Frontend.SourceCoreDirectLinking
