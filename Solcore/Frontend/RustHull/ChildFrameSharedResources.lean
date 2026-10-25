import Solcore.Frontend.RustHull.ChildFrameAllocationCorrespondence

/-! A child reuses the parent's shared references after earlier effects have
updated their values. Refreshing the proof inventory changes no reference or
location and reads the values from the current store. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution

def refreshCell (store : Store) (cell : InitializedCell) : InitializedCell :=
  {cell with value := (store.read? cell.location).getD .unit}

def refresh (store : Store) (cells : List InitializedCell) : List InitializedCell :=
  cells.map (refreshCell store)

theorem refresh_signature (store : Store) (cells : List InitializedCell) :
    (refresh store cells).map (fun cell => (cell.name, cell.type)) =
      cells.map (fun cell => (cell.name, cell.type)) := by
  simp only [refresh, List.map_map, Function.comp_def, refreshCell]

theorem refresh_references {depth : Nat} {environment : Environment}
    {references : AccountRuntime.References} {cells : List InitializedCell}
    (related : RuntimeReferences depth environment references cells) (store : Store) :
    RuntimeReferences depth environment references (refresh store cells) := by
  constructor
  · simpa only [refresh, List.map_map, Function.comp_def, refreshCell] using related.names
  · simp only [refresh, List.map_map]
    exact related.values

theorem refresh_stored {store : Store} {cells : List InitializedCell}
    (bounded : ∀ cell ∈ cells, cell.location < store.length) :
    InitializedCells (refresh store cells) store := by
  intro cell member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  have bound := bounded original originalMember
  have found : store.read? original.location = some (store[original.location]) :=
    List.getElem?_eq_getElem (bounded original originalMember)
  change store.read? original.location = some ((store.read? original.location).getD .unit)
  simp only [found, Option.getD_some]

theorem refresh_locations {store : Store} {cells : List InitializedCell} (separate : CellLocations cells) :
    CellLocations (refresh store cells) := by
  intro left leftMember right rightMember same
  obtain ⟨originalLeft, originalLeftMember, rfl⟩ := List.mem_map.mp leftMember
  obtain ⟨originalRight, originalRightMember, rfl⟩ := List.mem_map.mp rightMember
  exact separate originalLeft originalLeftMember originalRight originalRightMember same

/-- Value assertions are transported from the actual reads. A stale initial
value is never reused as evidence for a child frame. -/
theorem refresh_observed {store : Store} {cells : List InitializedCell}
    {accounts : StorageCorrespondence.Accounts} {state : RuntimeReturnDataEffectsSemantics.State}
    {bytes : List UInt8}
    (observed : ∀ cell ∈ cells, ∀ value, store.read? cell.location = some value →
      Observed accounts state bytes {cell with value := value})
    (bounded : ∀ cell ∈ cells, cell.location < store.length) :
    ∀ cell ∈ refresh store cells, Observed accounts state bytes cell := by
  intro cell member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  have bound := bounded original originalMember
  have found : store.read? original.location = some (store[original.location]) :=
    List.getElem?_eq_getElem (bounded original originalMember)
  simpa only [refreshCell, found, Option.getD_some] using observed original originalMember _ found

end Solcore.Frontend.RustHull.ChildFrameCorrespondence
