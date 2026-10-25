import Solcore.Frontend.RustHull.RuntimeInitializedEffects
import Solcore.Frontend.RustHull.RuntimeLogEffectsFrameCorrespondence

/-! Event cells are recovered from actual initialization, with their separation
from the other runtime cells derived from the allocator's named locations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLogInitializedEffects
open Correspondence ScalarExecution RuntimeInitializedEffects

structure Ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} (runtime : StateReady cells store state)
    (words : LogsSemantics.Words) (cursor : Core.Word) where
  layout : RuntimeLogEffectsCorrespondence.Layout
  base : layout.toLayout = RuntimeEffectsCorrespondence.initialLayout
    runtime.memoryRelated runtime.storageRelated runtime.distinct
  logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ cells.map InitializedCell.effectSlot
  logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ cells.map InitializedCell.effectSlot
  logsRead : store.read? layout.logs = some (Core.WordMapping.encode words)
  logSizeRead : store.read? layout.logSize = some (.word cursor)

theorem observe {cells : List InitializedCell} {store : Core.Store}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots)
    (initialized : InitializedCells cells store)
    {name : String} {type : Core.Ty} {value : Core.Value}
    (member : (name, type) ∈ Effects.slots)
    (observed : ∀ cell ∈ cells, cell.name = name → cell.value = value) :
    Nonempty (Cell cells store name type value) := by
  rw [← signature] at member
  obtain ⟨cell, present, same⟩ := List.mem_map.mp member
  obtain ⟨named, typed⟩ := Prod.mk.inj same
  exact ⟨cell, present, named, typed,
    by simpa only [observed cell present named] using initialized cell present⟩

theorem outside_runtime {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} (runtime : StateReady cells store state)
    (separate : CellLocations cells) {cell : InitializedCell} (member : cell ∈ cells)
    (outside : cell.name ∉ ["memory", "world", "address", "worldComplete", "isStatic",
      "exit", "returnOffset", "returnSize", "memorySize"]) :
    cell.location ∉ runtime.memory :: runtime.locations.all := by
  intro inside
  simp only [StorageBuiltinCorrespondence.Locations.all, List.mem_cons,
    List.not_mem_nil, or_false] at inside
  rcases inside with same | same | same | same | same | same | same | same | same
  all_goals
    first
    | exact cell_location_ne separate member runtime.memoryMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.worldMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.addressMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.completeMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.staticMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.exitMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.offsetMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.returnSizeMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.sizeMember (fun named => outside (by simp [named])) same

theorem ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {words : LogsSemantics.Words} {cursor : Core.Word}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (runtime : StateReady cells store state)
    (logsObserved : ∀ cell ∈ cells, cell.name = "logs" → cell.value = Core.WordMapping.encode words)
    (cursorObserved : ∀ cell ∈ cells, cell.name = "logSize" → cell.value = .word cursor) :
    Nonempty (Ready runtime words cursor) := by
  obtain ⟨logs⟩ := observe signature initialized (type := Core.WordMapping.type) (by simp [Effects.slots]) logsObserved
  obtain ⟨size⟩ := observe signature initialized (type := .word) (by simp [Effects.slots]) cursorObserved
  have logOutside := outside_runtime runtime separate logs.member (by rw [logs.named]; decide)
  have sizeOutside := outside_runtime runtime separate size.member (by rw [size.named]; decide)
  have different := separate.different logs.member size.member (by rw [logs.named, size.named]; decide)
  let layout : RuntimeLogEffectsCorrespondence.Layout := {
    toLayout := RuntimeEffectsCorrespondence.initialLayout runtime.memoryRelated runtime.storageRelated runtime.distinct
    logs := logs.cell.location
    logSize := size.cell.location
    jointDistinct := List.nodup_cons.mpr ⟨(by simpa only [RuntimeEffectsCorrespondence.initialLayout, List.mem_cons, not_or] using And.intro different logOutside),
      List.nodup_cons.mpr ⟨sizeOutside, runtime.distinct⟩⟩
    logsBelow := initialized.location_bound logs.member
    logSizeBelow := initialized.location_bound size.member }
  exact ⟨layout, rfl, logs.slot, size.slot, logs.stored, size.stored⟩

theorem Ready.passive_cell {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} (ready : Ready runtime words cursor)
    (separate : CellLocations cells) (initialized : InitializedCells cells store)
    {cell : InitializedCell} (member : cell ∈ cells)
    (outside : cell.name ∉ ["logs", "logSize", "memory", "memorySize", "world", "exit", "returnOffset", "returnSize"]) :
    RuntimeLogEffectsFrameCorrespondence.PassiveCell ready.layout
      (cells.map InitializedCell.effectSlot) store cell.name cell.value := by
  obtain ⟨slot, present, named, passive, below, stored⟩ := runtime.passive_cell separate initialized member
    (fun inside => outside (.tail _ (.tail _ inside)))
  refine ⟨slot, present, named, ?_, ?_, stored⟩
  · intro inside
    rcases List.mem_cons.mp inside with same | inside
    · obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp present
      exact cell_location_ne separate otherMember ready.logsMember
        (fun eq => outside (by simp [← named, InitializedCell.effectSlot, eq])) same
    rcases List.mem_cons.mp inside with same | inside
    · obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp present
      exact cell_location_ne separate otherMember ready.logSizeMember
        (fun eq => outside (by simp [← named, InitializedCell.effectSlot, eq])) same
    · exact passive (by simpa only [ready.base] using inside)
  · simpa only [ready.base] using below

end Solcore.Frontend.RustHull.RuntimeLogInitializedEffects
