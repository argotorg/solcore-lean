import Solcore.Frontend.RustHull.ChildCallbackContextCorrespondence

/-! The public object's actual shared and frame allocations supply the static
inventory used by child callbacks. No callback resource assumption is added to
the public source theorem. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractChildCallCorrespondence
open Core Correspondence ScalarExecution ContractCallCorrespondence
open ChildCallbackContextCorrespondence
open RuntimeCallEffectsCorrespondence (Layout sharedLocations)

theorem shared_signature {context : CodeBuilder.Code} {cells : List InitializedCell} {values : List Value}
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip values).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    (length : (AccountRuntime.sharedInitializers context).length ≤ values.length) :
    cells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse := by
  have typed := congrArg (List.map (fun entry : String × Core.Ty × Value => (entry.1, entry.2.1))) description
  simp only [List.map_reverse, List.map_map, Function.comp_def] at typed
  rw [typed]
  have firsts := List.map_fst_zip length
  have mapped := congrArg (List.map (fun entry : String × Core.Ty × CodeBuilder.Code => (entry.1, entry.2.1))) firsts
  simp only [List.map_map, Function.comp_def, sharedInitializers_types] at mapped
  exact congrArg List.reverse mapped

/-- The actual named frame references identify the five current shared
resources and every captured ambient cell. Bounds and separation come from the
same allocation, including the previously allocated creator cell. -/
theorem initialized_inventory {layout : Layout} {sharedCells cells : List InitializedCell}
    {initial store : Store} {creator : Nat} {withCode : Bool}
    (sharedSignature : sharedCells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    (signature : cells.map (fun cell => (cell.name, cell.type)) = RuntimeExtendedInitializedEffects.slots withCode)
    (stored : InitializedCells cells store) (separate : CellLocations cells)
    (boundary : layout.boundary = store.length)
    (members : ∀ slot ∈ RuntimeCallInitializedEffects.baseSlots layout.toReturnDataLayout,
      slot ∈ cells.map InitializedCell.effectSlot)
    (origin : ∀ cell ∈ cells, Origin sharedCells initial.length cell)
    (creatorAfter : ∀ cell ∈ sharedCells, cell.location < creator)
    (creatorBefore : creator < initial.length) (retainedLength : initial.length ≤ store.length) :
    Inventory layout sharedCells creator ∧
      (∀ cell ∈ sharedCells, cell.effectSlot ∈ cells.map InitializedCell.effectSlot) := by
  have included := shared_included sharedSignature signature origin
  have shared : SharedCells sharedCells (sharedLocations layout) :=
    RuntimeCallInitializedEffects.shared_cells members (fun cell member named => (origin cell member).1 (by
      simp only [dispatchSharedNames, List.mem_cons, List.not_mem_nil, or_false] at named
      rcases named with named | named | named | named | named
      all_goals simp [named, sharedSlotTypes]))
  refine ⟨⟨sharedSignature, shared, separate.subset included, ?_, ?_, ?_,
    ambient_outside included separate members, creator_outside creatorBefore creatorAfter origin members⟩,
    fun cell member => List.mem_map_of_mem (included cell member)⟩
  · intro cell member
    rw [boundary]
    exact stored.location_bound (included cell member)
  · rw [boundary]
    exact Nat.lt_of_lt_of_le creatorBefore retainedLength
  · exact fun cell member => Nat.ne_of_lt (creatorAfter cell member)

/-- A callback's original captured reference expressions still denote the
same five runtime locations identified by the actual frame allocator. -/
theorem inventory_references {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator)
    {depth : Nat} {environment : Environment} {shared : AccountRuntime.References}
    (references : RuntimeReferences depth environment shared cells) :
    AccountCallCorrespondence.SharedReferences depth environment shared (sharedLocations layout) :=
  inventory.shared.references inventory.unique references

/-- Context initialization follows the shared allocation's real contents and
the actual optional creator cell, even after subsequent frame allocations. -/
theorem initialized_context {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {initial store : Store}
    (stored : InitializedCells cells initial) (creatorPresent : ∃ value, initial.read? creator = some value)
    (retained : StoreRetains initial store) :
    (ChildCallbackContextCorrespondence.context inventory).valid (prefixRead layout.boundary store) := by
  apply ChildCallbackContextCorrespondence.initial inventory (stored.retained retained)
  obtain ⟨value, found⟩ := creatorPresent
  exact ⟨value, (retained.read creator (List.getElem?_eq_some_iff.mp found).1).trans found⟩

end Solcore.Frontend.RustHull.ContractChildCallCorrespondence
