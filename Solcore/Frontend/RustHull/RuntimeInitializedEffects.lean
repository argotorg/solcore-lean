import Solcore.Frontend.RustHull.RuntimeAllocationLocations
import Solcore.Frontend.RustHull.RuntimeEffectsFrameCorrespondence
import Solcore.Frontend.RustHull.RuntimeEnvironmentCorrespondence

/-! The actual allocator's named cells establish the concrete memory and
storage state relation, including every required disjoint location. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeInitializedEffects
open Correspondence ScalarExecution

def expected (accounts : StorageCorrespondence.Accounts) (state : RuntimeEffectsSemantics.State) :
    String → Option Core.Value
  | "memory" => some (Core.WordMapping.encode state.memory.words)
  | "memorySize" => some (.word state.memory.size)
  | "world" => some (StorageCorrespondence.world accounts)
  | "address" => some (.word state.storage.address)
  | "worldComplete" => some (.bool state.storage.complete)
  | "isStatic" => some (.bool state.storage.isStatic)
  | "exit" => some (.word state.storage.exit)
  | "returnOffset" => some (.word state.storage.returnOffset)
  | "returnSize" => some (.word state.storage.returnSize)
  | _ => none

def Observed (accounts : StorageCorrespondence.Accounts) (state : RuntimeEffectsSemantics.State)
    (cell : InitializedCell) : Prop :=
  ∀ value, expected accounts state cell.name = some value → cell.value = value

structure Cell (cells : List InitializedCell) (store : Core.Store)
    (name : String) (type : Core.Ty) (value : Core.Value) where
  cell : InitializedCell
  member : cell ∈ cells
  named : cell.name = name
  typed : cell.type = type
  stored : store.read? cell.location = some value

theorem Cell.slot {cells : List InitializedCell} {store : Core.Store}
    {name : String} {type : Core.Ty} {value : Core.Value}
    (selected : Cell cells store name type value) :
    ⟨name, type, selected.cell.location⟩ ∈ cells.map InitializedCell.effectSlot := by
  exact List.mem_map.mpr ⟨selected.cell, selected.member,
    by simp only [InitializedCell.effectSlot, selected.named, selected.typed]⟩

theorem observe {cells : List InitializedCell} {store : Core.Store}
    {accounts : StorageCorrespondence.Accounts} {state : RuntimeEffectsSemantics.State}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots)
    (initialized : InitializedCells cells store)
    (observed : ∀ cell ∈ cells, Observed accounts state cell)
    {name : String} {type : Core.Ty} {value : Core.Value}
    (member : (name, type) ∈ Effects.slots)
    (specified : expected accounts state name = some value) :
    Nonempty (Cell cells store name type value) := by
  rw [← signature] at member
  obtain ⟨cell, present, same⟩ := List.mem_map.mp member
  obtain ⟨named, typed⟩ := Prod.mk.inj same
  have valued := observed cell present value (by simpa only [named] using specified)
  exact ⟨cell, present, named, typed, by simpa only [valued] using initialized cell present⟩

structure StateReady (cells : List InitializedCell) (store : Core.Store)
    (state : RuntimeEffectsSemantics.State) where
  memory : Nat
  locations : StorageBuiltinCorrespondence.Locations
  memoryMember : ⟨"memory", Core.WordMapping.type, memory⟩ ∈ cells.map InitializedCell.effectSlot
  worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ cells.map InitializedCell.effectSlot
  addressMember : ⟨"address", .word, locations.address⟩ ∈ cells.map InitializedCell.effectSlot
  completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ cells.map InitializedCell.effectSlot
  staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ cells.map InitializedCell.effectSlot
  sizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ cells.map InitializedCell.effectSlot
  exitMember : ⟨"exit", .word, locations.exit⟩ ∈ cells.map InitializedCell.effectSlot
  offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ cells.map InitializedCell.effectSlot
  returnSizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ cells.map InitializedCell.effectSlot
  memoryRelated : MemoryCorrespondence.StateRel memory locations.memorySize state.memory store
  storageRelated : StorageBuiltinCorrespondence.StateRel locations state.storage store
  distinct : (memory :: locations.all).Nodup

/-- Every input is an observation of the real initialized cells. No abstract
runtime layout or aliasing condition is assumed. -/
theorem state_ready {cells : List InitializedCell} {store : Core.Store}
    {accounts : StorageCorrespondence.Accounts} {state : RuntimeEffectsSemantics.State}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (observed : ∀ cell ∈ cells, Observed accounts state cell)
    (world : accounts.map Prod.fst = state.storage.world) :
    Nonempty (StateReady cells store state) := by
  obtain ⟨memory⟩ := observe signature initialized observed (name := "memory") (type := Core.WordMapping.type) (by simp [Effects.slots]) rfl
  obtain ⟨size⟩ := observe signature initialized observed (name := "memorySize") (type := .word) (by simp [Effects.slots]) rfl
  obtain ⟨worldCell⟩ := observe signature initialized observed (name := "world") (type := AccountState.type) (by simp [Effects.slots]) rfl
  obtain ⟨address⟩ := observe signature initialized observed (name := "address") (type := .word) (by simp [Effects.slots]) rfl
  obtain ⟨complete⟩ := observe signature initialized observed (name := "worldComplete") (type := .bool) (by simp [Effects.slots]) rfl
  obtain ⟨isStatic⟩ := observe signature initialized observed (name := "isStatic") (type := .bool) (by simp [Effects.slots]) rfl
  obtain ⟨exit⟩ := observe signature initialized observed (name := "exit") (type := .word) (by simp [Effects.slots]) rfl
  obtain ⟨offset⟩ := observe signature initialized observed (name := "returnOffset") (type := .word) (by simp [Effects.slots]) rfl
  obtain ⟨returnSize⟩ := observe signature initialized observed (name := "returnSize") (type := .word) (by simp [Effects.slots]) rfl
  let selected := [memory.cell, worldCell.cell, address.cell, complete.cell, isStatic.cell,
    exit.cell, offset.cell, returnSize.cell, size.cell]
  have included : ∀ cell ∈ selected, cell ∈ cells := by
    intro cell member
    simp only [selected, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact memory.member
      | exact worldCell.member
      | exact address.member
      | exact complete.member
      | exact isStatic.member
      | exact exit.member
      | exact offset.member
      | exact returnSize.member
      | exact size.member
  have names : (selected.map InitializedCell.name).Nodup := by
    simp only [selected, List.map_cons, List.map_nil, memory.named, worldCell.named, address.named,
      complete.named, isStatic.named, exit.named, offset.named, returnSize.named, size.named]
    decide
  have distinct := (separate.subset included).nodup names
  let locations : StorageBuiltinCorrespondence.Locations :=
    ⟨worldCell.cell.location, address.cell.location, complete.cell.location, isStatic.cell.location,
      exit.cell.location, offset.cell.location, returnSize.cell.location, size.cell.location⟩
  have joint : (memory.cell.location :: locations.all).Nodup := distinct
  refine ⟨⟨memory.cell.location, locations, memory.slot, worldCell.slot, address.slot,
    complete.slot, isStatic.slot, size.slot, exit.slot, offset.slot, returnSize.slot,
    ⟨?_, memory.stored, size.stored⟩, ?_, joint⟩⟩
  · exact separate.different memory.member size.member (by simp only [memory.named, size.named]; decide)
  · exact ⟨⟨accounts, world, worldCell.stored⟩, address.stored, complete.stored, isStatic.stored,
      exit.stored, offset.stored, returnSize.stored, (List.nodup_cons.mp joint).2⟩

theorem cell_location_ne {cells : List InitializedCell} (separate : CellLocations cells)
    {cell : InitializedCell} (member : cell ∈ cells) {slot : EffectSlot}
    (slotMember : slot ∈ cells.map InitializedCell.effectSlot) (different : cell.name ≠ slot.name) :
    cell.location ≠ slot.location := by
  obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp slotMember
  exact separate.different member otherMember different

theorem StateReady.passive_cell {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} (ready : StateReady cells store state)
    (separate : CellLocations cells) (initialized : InitializedCells cells store)
    {cell : InitializedCell} (member : cell ∈ cells)
    (outside : cell.name ∉ ["memory", "memorySize", "world", "exit", "returnOffset", "returnSize"]) :
    RuntimeEffectsFrameCorrespondence.PassiveCell
      (RuntimeEffectsCorrespondence.initialLayout ready.memoryRelated ready.storageRelated ready.distinct)
      (cells.map InitializedCell.effectSlot) store cell.name cell.value := by
  refine ⟨cell.effectSlot, List.mem_map.mpr ⟨cell, member, rfl⟩, rfl, ?_,
    initialized.location_bound member, initialized cell member⟩
  intro inside
  change cell.location ∈ [ready.memory, ready.locations.memorySize] ++ ready.locations.mutable at inside
  simp only [StorageBuiltinCorrespondence.Locations.mutable, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at inside
  rcases inside with (same | same) | same | same | same | same
  · exact cell_location_ne separate member ready.memoryMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member ready.sizeMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member ready.worldMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member ready.exitMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member ready.offsetMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member ready.returnSizeMember (fun named => outside (by simp [named])) same

end Solcore.Frontend.RustHull.RuntimeInitializedEffects
