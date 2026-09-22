import Solcore.Frontend.SourceProgramExecution

/-! Small checked laws for the public single-seed source execution pipeline. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceProgramExecution

@[simp] theorem PreparedEntry.key_eq_entry (prepared : PreparedEntry) :
    prepared.key = prepared.entry.key := by
  rfl

@[simp] theorem PreparedEntry.inputTypes_eq_entry (prepared : PreparedEntry) :
    prepared.inputTypes = prepared.entry.elaborated.inputs.values := by
  rfl

@[simp] theorem PreparedEntry.run?_eq_entry (prepared : PreparedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store) :
    prepared.run? inputs fuel store = prepared.entry.run? inputs fuel store := by
  rfl

theorem PreparedEntry.run?_of_matching_types (prepared : PreparedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store)
    (finite : prepared.entry.runtime = none)
    (typesEqual : inputs.map Core.Value.type = prepared.inputTypes) :
    prepared.run? inputs fuel store = some (Core.runStateful fuel
      (Core.State.initial prepared.entry.elaborated.core inputs store)) := by
  simp [PreparedEntry.run?, SourceCoreDirectLinking.LinkedEntry.run?,
    PreparedEntry.inputTypes, finite, typesEqual]

theorem PreparedEntry.run?_of_mismatched_types (prepared : PreparedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store)
    (mismatch : inputs.map Core.Value.type ≠ prepared.inputTypes) :
    prepared.run? inputs fuel store = none := by
  change inputs.map Core.Value.type ≠
    prepared.entry.elaborated.inputs.values at mismatch
  simp [PreparedEntry.run?, SourceCoreDirectLinking.LinkedEntry.run?,
    mismatch]

theorem run_of_prepared (raw : Workspace.RawWorkspace) (seed : Seed)
    (inputs : List Core.Value) (limits : Limits) (store : Core.Store)
    (prepared : PreparedEntry)
    (preparedOk : prepare raw seed limits = .ok prepared) :
    run raw seed inputs limits store =
      match prepared.run? inputs limits.executionFuel store with
      | some result => .ok result
      | none => .error (.inputTypesMismatch prepared.inputTypes
          (inputs.map Core.Value.type)) := by
  unfold run
  rw [preparedOk]
  rfl

theorem run_of_prepared_matching_types (raw : Workspace.RawWorkspace)
    (seed : Seed) (inputs : List Core.Value) (limits : Limits)
    (store : Core.Store) (prepared : PreparedEntry)
    (preparedOk : prepare raw seed limits = .ok prepared)
    (finite : prepared.entry.runtime = none)
    (typesEqual : inputs.map Core.Value.type = prepared.inputTypes) :
    run raw seed inputs limits store = .ok (Core.runStateful
      limits.executionFuel
      (Core.State.initial prepared.entry.elaborated.core inputs store)) := by
  rw [run_of_prepared raw seed inputs limits store prepared preparedOk]
  rw [PreparedEntry.run?_of_matching_types prepared inputs
    limits.executionFuel store finite typesEqual]

theorem run_of_prepared_mismatched_types (raw : Workspace.RawWorkspace)
    (seed : Seed) (inputs : List Core.Value) (limits : Limits)
    (store : Core.Store) (prepared : PreparedEntry)
    (preparedOk : prepare raw seed limits = .ok prepared)
    (mismatch : inputs.map Core.Value.type ≠ prepared.inputTypes) :
    run raw seed inputs limits store = .error (.inputTypesMismatch
      prepared.inputTypes (inputs.map Core.Value.type)) := by
  rw [run_of_prepared raw seed inputs limits store prepared preparedOk]
  rw [PreparedEntry.run?_of_mismatched_types prepared inputs
    limits.executionFuel store mismatch]

end Solcore.Frontend.SourceProgramExecution
