import Solcore.Frontend.RustHull.RuntimeLogEffectsCorrespondence

/-! Concrete initialized log values extend the already established runtime
relation. Distinct cell names establish environment-read separation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLogEffectsCorrespondence
open Correspondence ScalarExecution

theorem initial_state {layout : Layout} {slots : List EffectSlot} {state : RuntimeLogEffectsSemantics.State}
    {store : Core.Store}
    (runtime : StateRel (RuntimeEnvironmentEffectsCorrespondence.model layout.toLayout
      (prefixRead layout.boundary store) slots) [] ⟨[], state.runtime⟩ store)
    (logs : store.read? layout.logs = some (Core.WordMapping.encode state.words))
    (cursor : store.read? layout.logSize = some (.word state.cursor)) :
    StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], state⟩ store := by
  have logsRead : prefixRead layout.boundary store layout.logs = some (Core.WordMapping.encode state.words) := by
    simpa only [prefixRead, layout.logsBelow, ↓reduceIte] using logs
  have cursorRead : prefixRead layout.boundary store layout.logSize = some (.word state.cursor) := by
    simpa only [prefixRead, layout.logSizeBelow, ↓reduceIte] using cursor
  have unchanged : patched layout (prefixRead layout.boundary store) state = prefixRead layout.boundary store := by
    funext location
    unfold patched
    split
    · subst location; exact logsRead.symm
    · split
      · subst location; exact cursorRead.symm
      · rfl
  exact ⟨runtime.toHeapRel, runtime.external.1, runtime.external.2.1,
    by simpa only [unchanged] using runtime.external.2.2, logsRead, cursorRead⟩

theorem Passive.of_names {layout : Layout} {slots : List EffectSlot}
    (names : ∀ first ∈ slots, ∀ second ∈ slots, first.location = second.location → first.name = second.name)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots) : Passive layout slots := by
  have runtimePassive := RuntimeEnvironmentEffectsCorrespondence.Passive.of_names names memoryMember worldMember memorySizeMember
    exitMember offsetMember sizeMember
  intro slot member state value observed inside
  rcases List.mem_cons.mp inside with same | inside
  · have named := names slot member _ logsMember same
    rw [named] at observed
    cases slot.type <;> contradiction
  rcases List.mem_cons.mp inside with same | inside
  · have named := names slot member _ logSizeMember same
    rw [named] at observed
    cases slot.type <;> contradiction
  · exact runtimePassive slot member state value observed inside

end Solcore.Frontend.RustHull.RuntimeLogEffectsCorrespondence
