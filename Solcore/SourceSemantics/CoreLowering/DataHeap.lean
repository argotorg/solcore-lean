import Solcore.SourceSemantics.CoreLowering.DataValueTyping
import Solcore.SourceSemantics.CoreLowering.GeneralHeapFrame

/-! A catalog-indexed heap relation for ordinary finite data cells. Values use
the same authenticated relation as pattern and member proofs. The whole Core
store is typed against the actual catalog, including arbitrary administrative
closures. Generalized closures, functions and mappings in source cells are not
part of this finite value profile. Source and Core locations need not coincide.
-/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataHeap
open Frontend Frontend.SourceInference TypeSystem GeneralHeap DataPatternTypedValues

inductive CellRepresents (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures) :
    Dynamic.Cell → Core.Value → Core.Ty → Prop where
  | uninitialized {sourceType : Ty} {payload : Core.Ty}
      (projection : catalog.project sourceType = .ok payload) :
      CellRepresents catalog signatures ⟨sourceType, none, none⟩ (.inLeft payload .unit) payload
  | initialized {sourceType : Ty} {payload : Core.Ty} {source : Dynamic.Value} {value : Core.Value}
      (projection : catalog.project sourceType = .ok payload)
      (represented : TypedValueRep catalog signatures sourceType source value) :
      CellRepresents catalog signatures ⟨sourceType, some source, none⟩ (.inRight .unit value) payload

theorem CellRepresents.projection {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (represented : CellRepresents catalog signatures cell value payload) :
    catalog.project cell.type = .ok payload := by cases represented <;> assumption

theorem CellRepresents.ordinary {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (represented : CellRepresents catalog signatures cell value payload) : cell.generalized = none := by
  cases represented <;> rfl

theorem CellRepresents.runtime_hasType {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (represented : CellRepresents catalog signatures cell value payload) (world : Core.StoreTyping) :
    Core.RuntimeValueHasType world value (Core.OptionalCell.cellType payload) catalog.definitions := by
  cases represented with
  | uninitialized => exact .inLeft .unit
  | initialized projection related =>
    obtain ⟨type, projected, typed⟩ := DataValueTyping.TypedValueRep.project_typed related
    have same := Except.ok.inj (projected.symm.trans projection)
    subst type
    exact .inRight (typed world)

private theorem append_lookup {mapping : LocationMap} {fresh index target : Nat}
    (found : (mapping ++ [fresh])[index]? = some target) :
    mapping[index]? = some target ∨ (index = mapping.length ∧ target = fresh) := by
  by_cases old : index < mapping.length
  · left; rwa [List.getElem?_append_left old] at found
  · right
    have bound := (List.getElem?_eq_some_iff.mp found).1
    have same : index = mapping.length := by simp only [List.length_append, List.length_singleton] at bound; omega
    subst index
    exact ⟨rfl, by simpa using found.symm⟩

structure HeapRepresents (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures) (mapping : LocationMap) (world : Core.StoreTyping)
    (heap : Dynamic.Heap) (store : Core.Store) : Prop where
  length_eq : mapping.length = heap.cells.length
  injective : LocationMap.Injective mapping
  runtime_hasTypes : Core.RuntimeStoreHasTypes world store catalog.definitions
  cells : ∀ {source target : Nat}, mapping[source]? = some target →
    ∃ cell value payload,
      Dynamic.Heap.Reads heap ⟨source⟩ cell ∧
      world[target]? = some (Core.OptionalCell.cellType payload) ∧
      store.read? target = some value ∧ CellRepresents catalog signatures cell value payload

variable {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}

theorem HeapRepresents.empty : HeapRepresents catalog signatures [] [] ⟨[]⟩ [] := by
  refine ⟨rfl, ?_, Core.RuntimeStoreHasTypes.nil catalog.definitions, ?_⟩
  · intro left right target impossible; simp at impossible
  · intro source target impossible; simp at impossible

theorem HeapRepresents.target_lt {mapping : LocationMap} {world : Core.StoreTyping}
    {heap : Dynamic.Heap} {store : Core.Store} (related : HeapRepresents catalog signatures mapping world heap store)
    {source target : Nat} (mapped : mapping[source]? = some target) : target < store.length := by
  obtain ⟨_, _, _, _, typed, _, _⟩ := related.cells mapped
  exact related.runtime_hasTypes.location_lt typed

theorem HeapRepresents.read {mapping : LocationMap} {world : Core.StoreTyping}
    {heap : Dynamic.Heap} {store : Core.Store} (related : HeapRepresents catalog signatures mapping world heap store)
    {location : Dynamic.Location} {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads heap location cell) :
    ∃ target value payload,
      ReferenceRepresents mapping world location target payload ∧
      store.read? target = some value ∧ CellRepresents catalog signatures cell value payload := by
  have bound : location.index < mapping.length := by rw [related.length_eq]; exact read.location_valid
  have mapped := List.getElem?_eq_getElem bound
  obtain ⟨selected, value, payload, sourceRead, typed, coreRead, represents⟩ := related.cells mapped
  have same := read.functional sourceRead
  subst selected
  exact ⟨_, value, payload, ⟨mapped, typed⟩, coreRead, represents⟩

/-- Appending an administrative cell changes neither the source heap nor its
location map. Its payload can be a closure or reference; scalar store typing is
not required or derived. -/
theorem HeapRepresents.allocate_administrative
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store : Core.Store}
    (related : HeapRepresents catalog signatures mapping world heap store) {value : Core.Value} {type : Core.Ty}
    (typed : Core.RuntimeValueHasType world value type catalog.definitions) :
    HeapRepresents catalog signatures mapping (world ++ [type]) heap (store.allocate value).1 := by
  refine ⟨related.length_eq, related.injective, related.runtime_hasTypes.allocate typed, ?_⟩
  intro source target mapped
  obtain ⟨cell, old, payload, sourceRead, found, coreRead, represents⟩ := related.cells mapped
  exact ⟨cell, old, payload, sourceRead, (Core.WorldExtends.lookup ⟨[type], rfl⟩ found),
    (Core.Store.allocate_old_lookup store value (related.target_lt mapped)).trans coreRead, represents⟩

/-- Mapped source allocation appends at the source heap length, while Core
allocation appends at the independent Core store length. Only the map grows. -/
theorem HeapRepresents.allocate
    {mapping : LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap} {store : Core.Store}
    {sourceType : Ty} {sourceValue : Option Dynamic.Value} {location : Dynamic.Location}
    {value : Core.Value} {payload : Core.Ty}
    (related : HeapRepresents catalog signatures mapping world heap store)
    (cell : CellRepresents catalog signatures { type := sourceType, value := sourceValue } value payload)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    HeapRepresents catalog signatures (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      after (store.allocate value).1 ∧
    ReferenceRepresents (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      location store.length payload := by
  cases allocated
  have extension : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
  have freshType : (world ++ [Core.OptionalCell.cellType payload])[store.length]? =
      some (Core.OptionalCell.cellType payload) := by rw [← related.runtime_hasTypes.length_eq]; simp
  have freshMap : (mapping ++ [store.length])[heap.cells.length]? = some store.length := by
    rw [← related.length_eq]; simp
  refine ⟨⟨?_, LocationMap.Injective.append related.injective store.length ?_,
    related.runtime_hasTypes.allocate (cell.runtime_hasType world), ?_⟩, ⟨freshMap, freshType⟩⟩
  · simp [related.length_eq]
  · intro index impossible
    have bound := related.target_lt impossible
    omega
  · intro source target mapped
    rcases append_lookup mapped with old | ⟨sourceEq, targetEq⟩
    · obtain ⟨oldCell, oldValue, oldPayload, sourceRead, found, coreRead, represents⟩ := related.cells old
      exact ⟨oldCell, oldValue, oldPayload, Dynamic.Heap.Allocates.preserves_read .append sourceRead,
        extension.lookup found,
        (Core.Store.allocate_old_lookup store value (related.target_lt old)).trans coreRead, represents⟩
    · subst target
      rw [related.length_eq] at sourceEq
      subst source
      exact ⟨_, value, payload, Dynamic.Heap.Allocates.reads_new .append, freshType,
        Core.Store.allocate_fresh_lookup store value, cell⟩

/-- A well-typed write to an unmapped administrative cell preserves the source
heap and every source-visible cell. This permits installing recursive closures
after allocating their optional administrative function cells. -/
theorem HeapRepresents.write_administrative
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap}
    {store updated : Core.Store} {location : Core.Location} {type : Core.Ty} {value : Core.Value}
    (related : HeapRepresents catalog signatures mapping world heap store)
    (absent : ∀ {source : Nat}, mapping[source]? ≠ some location)
    (found : world[location]? = some type) (typed : Core.RuntimeValueHasType world value type catalog.definitions)
    (written : store.write? location value = some updated) :
    HeapRepresents catalog signatures mapping world heap updated := by
  refine ⟨related.length_eq, related.injective, related.runtime_hasTypes.write found typed written, ?_⟩
  intro source target mapped
  obtain ⟨cell, stored, payload, sourceRead, typed, coreRead, represents⟩ := related.cells mapped
  have different : target ≠ location := by intro same; exact absent (same ▸ mapped)
  exact ⟨cell, stored, payload, sourceRead, typed,
    (Core.Store.write?_preserves_other written different).trans coreRead, represents⟩

/-- Structural replacement changes only the mapped Core location. Map
injectivity is what prevents a write from changing a distinct source cell. -/
theorem HeapRepresents.replace
    {mapping : LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap} {store : Core.Store}
    {location : Dynamic.Location} {target : Core.Location} {payload : Core.Ty}
    {replacement : Dynamic.Cell} {value : Core.Value}
    (related : HeapRepresents catalog signatures mapping world heap store)
    (reference : ReferenceRepresents mapping world location target payload)
    (written : Dynamic.Heap.CellsWrite heap.cells location.index replacement after.cells)
    (newCell : CellRepresents catalog signatures replacement value payload) :
    ∃ updated, store.write? target value = some updated ∧
      HeapRepresents catalog signatures mapping world after updated := by
  obtain ⟨updated, coreWritten⟩ := related.runtime_hasTypes.write_exists (value := value) reference.typed
  refine ⟨updated, coreWritten, ⟨related.length_eq.trans written.length_eq.symm,
    related.injective, related.runtime_hasTypes.write reference.typed
      (newCell.runtime_hasType world) coreWritten, ?_⟩⟩
  intro source other mapped
  obtain ⟨cell, stored, storedType, sourceRead, found, coreRead, represents⟩ := related.cells mapped
  by_cases same : source = location.index
  · subst source
    have targetEq : other = target := Option.some.inj (mapped.symm.trans reference.mapped)
    subst other
    exact ⟨replacement, value, payload, .intro written.reads_replacement,
      reference.typed, Core.Store.write?_reads_written coreWritten, newCell⟩
  · have different : other ≠ target := by
      intro equal
      exact same (related.injective (equal ▸ mapped) reference.mapped)
    cases sourceRead with
    | intro sourceAt =>
        exact ⟨cell, stored, storedType, .intro (written.preserves_other same sourceAt), found,
          (Core.Store.write?_preserves_other coreWritten different).trans coreRead, represents⟩

/-- Writes retain the source declaration's type. The replacement is
independently authenticated at that exact type; a coincident Core projection
alone cannot establish equality of nominal source types. -/
theorem HeapRepresents.write_initialized
    {mapping : LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap} {store : Core.Store}
    {location : Dynamic.Location} {target : Core.Location} {payload : Core.Ty}
    {cell : Dynamic.Cell} {sourceValue : Dynamic.Value} {value : Core.Value}
    (related : HeapRepresents catalog signatures mapping world heap store)
    (reference : ReferenceRepresents mapping world location target payload)
    (read : Dynamic.Heap.Reads heap location cell)
    (represented : TypedValueRep catalog signatures cell.type sourceValue value)
    (written : Dynamic.Heap.Writes heap location (some sourceValue) after) :
    ∃ updated, store.write? target (.inRight .unit value) = some updated ∧
      HeapRepresents catalog signatures mapping world after updated ∧
      AdministrativePreserved mapping store mapping updated := by
  cases written with
  | @intro previous cells previousRead written =>
    have same := read.functional previousRead
    subst previous
    obtain ⟨old, oldValue, oldPayload, oldRead, found, _, oldRelated⟩ := related.cells reference.mapped
    have same := read.functional oldRead
    subst old
    have samePayload : oldPayload = payload := by
      simpa [Core.OptionalCell.cellType] using Option.some.inj (found.symm.trans reference.typed)
    subst oldPayload
    have projection := oldRelated.projection
    have ordinary := oldRelated.ordinary
    have replacement : CellRepresents catalog signatures { cell with value := some sourceValue }
        (.inRight .unit value) payload := by
      cases cell
      simp only at ordinary projection represented ⊢
      subst_vars
      exact .initialized projection represented
    obtain ⟨updated, coreWritten, finalRelated⟩ := related.replace reference written replacement
    exact ⟨updated, coreWritten, finalRelated,
      AdministrativePreserved.write (List.mem_of_getElem? reference.mapped) coreWritten⟩

end Solcore.SourceSemantics.CoreLowering.DataHeap
