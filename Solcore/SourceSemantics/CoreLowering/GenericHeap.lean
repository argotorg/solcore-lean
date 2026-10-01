import Solcore.SourceSemantics.CoreLowering.GenericHeapPayload

/-! Common location-map/world/admin-frame machinery for ordinary optional source
cells. The payload model may contain authenticated mapping, function or proxy
representations. This module proves heap representation preservation only;
payload language semantics and callable-body correspondence remain separate.
The existing finite DataHeap is recovered exactly by finiteHeap_iff. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericHeap
open Frontend Frontend.SourceInference TypeSystem GeneralHeap

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

structure HeapRepresents {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection} (model : PayloadModel catalog projects) (mapping : LocationMap) (world : Core.StoreTyping)
    (heap : Dynamic.Heap) (store : Core.Store) : Prop where
  length_eq : mapping.length = heap.cells.length
  injective : LocationMap.Injective mapping
  runtime_hasTypes : Core.RuntimeStoreHasTypes world store catalog.definitions
  cells : ∀ {source target : Nat}, mapping[source]? = some target →
    ∃ cell value payload,
      Dynamic.Heap.Reads heap ⟨source⟩ cell ∧
      world[target]? = some (Core.OptionalCell.cellType payload) ∧
      store.read? target = some value ∧ CellRepresents model mapping world cell value payload

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection} {model : PayloadModel catalog projects}

theorem HeapRepresents.empty : HeapRepresents model [] [] ⟨[]⟩ [] := by
  refine ⟨rfl, ?_, Core.RuntimeStoreHasTypes.nil catalog.definitions, ?_⟩
  · intro left right target impossible; simp at impossible
  · intro source target impossible; simp at impossible

theorem HeapRepresents.target_lt {mapping : LocationMap} {world : Core.StoreTyping}
    {heap : Dynamic.Heap} {store : Core.Store} (related : HeapRepresents model mapping world heap store)
    {source target : Nat} (mapped : mapping[source]? = some target) : target < store.length := by
  obtain ⟨_, _, _, _, typed, _, _⟩ := related.cells mapped
  exact related.runtime_hasTypes.location_lt typed

theorem HeapRepresents.read {mapping : LocationMap} {world : Core.StoreTyping}
    {heap : Dynamic.Heap} {store : Core.Store} (related : HeapRepresents model mapping world heap store)
    {location : Dynamic.Location} {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads heap location cell) :
    ∃ target value payload,
      ReferenceRepresents mapping world location target payload ∧
      store.read? target = some value ∧ CellRepresents model mapping world cell value payload := by
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
    (related : HeapRepresents model mapping world heap store) {value : Core.Value} {type : Core.Ty}
    (typed : Core.RuntimeValueHasType world value type catalog.definitions) :
    HeapRepresents model mapping (world ++ [type]) heap (store.allocate value).1 := by
  refine ⟨related.length_eq, related.injective, related.runtime_hasTypes.allocate typed, ?_⟩
  intro source target mapped
  obtain ⟨cell, old, payload, sourceRead, found, coreRead, represents⟩ := related.cells mapped
  exact ⟨cell, old, payload, sourceRead, (Core.WorldExtends.lookup ⟨[type], rfl⟩ found),
    (Core.Store.allocate_old_lookup store value (related.target_lt mapped)).trans coreRead,
    represents.extend (.refl _) ⟨[type], rfl⟩⟩

/-- Mapped source allocation appends at the source heap length, while Core
allocation appends at the independent Core store length. Only the map grows. -/
theorem HeapRepresents.allocate
    {mapping : LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap} {store : Core.Store}
    {sourceType : Ty} {sourceValue : Option Dynamic.Value} {location : Dynamic.Location}
    {value : Core.Value} {payload : Core.Ty}
    (related : HeapRepresents model mapping world heap store)
    (cell : CellRepresents model mapping world { type := sourceType, value := sourceValue } value payload)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    HeapRepresents model (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
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
    related.runtime_hasTypes.allocate (cell.runtime_hasType), ?_⟩, ⟨freshMap, freshType⟩⟩
  · simp [related.length_eq]
  · intro index impossible
    have bound := related.target_lt impossible
    omega
  · intro source target mapped
    rcases append_lookup mapped with old | ⟨sourceEq, targetEq⟩
    · obtain ⟨oldCell, oldValue, oldPayload, sourceRead, found, coreRead, represents⟩ := related.cells old
      exact ⟨oldCell, oldValue, oldPayload, Dynamic.Heap.Allocates.preserves_read .append sourceRead,
        extension.lookup found,
        (Core.Store.allocate_old_lookup store value (related.target_lt old)).trans coreRead,
        represents.extend ⟨[store.length], rfl⟩ extension⟩
    · subst target
      rw [related.length_eq] at sourceEq
      subst source
      exact ⟨_, value, payload, Dynamic.Heap.Allocates.reads_new .append, freshType,
        Core.Store.allocate_fresh_lookup store value, cell.extend ⟨[store.length], rfl⟩ extension⟩

/-- A well-typed write to an unmapped administrative cell preserves the source
heap and every source-visible cell. This permits installing recursive closures
after allocating their optional administrative function cells. -/
theorem HeapRepresents.write_administrative
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap}
    {store updated : Core.Store} {location : Core.Location} {type : Core.Ty} {value : Core.Value}
    (related : HeapRepresents model mapping world heap store)
    (absent : ∀ {source : Nat}, mapping[source]? ≠ some location)
    (found : world[location]? = some type) (typed : Core.RuntimeValueHasType world value type catalog.definitions)
    (written : store.write? location value = some updated) :
    HeapRepresents model mapping world heap updated := by
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
    (related : HeapRepresents model mapping world heap store)
    (reference : ReferenceRepresents mapping world location target payload)
    (written : Dynamic.Heap.CellsWrite heap.cells location.index replacement after.cells)
    (newCell : CellRepresents model mapping world replacement value payload) :
    ∃ updated, store.write? target value = some updated ∧
      HeapRepresents model mapping world after updated := by
  obtain ⟨updated, coreWritten⟩ := related.runtime_hasTypes.write_exists (value := value) reference.typed
  refine ⟨updated, coreWritten, ⟨related.length_eq.trans written.length_eq.symm,
    related.injective, related.runtime_hasTypes.write reference.typed
      (newCell.runtime_hasType) coreWritten, ?_⟩⟩
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
    (related : HeapRepresents model mapping world heap store)
    (reference : ReferenceRepresents mapping world location target payload)
    (read : Dynamic.Heap.Reads heap location cell)
    (represented : model.Represents mapping world cell.type sourceValue value payload)
    (written : Dynamic.Heap.Writes heap location (some sourceValue) after) :
    ∃ updated, store.write? target (.inRight .unit value) = some updated ∧
      HeapRepresents model mapping world after updated ∧
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
    have replacement : CellRepresents model mapping world { cell with value := some sourceValue }
        (.inRight .unit value) payload := by
      cases cell
      simp only at ordinary projection represented ⊢
      subst_vars
      exact .initialized represented
    obtain ⟨updated, coreWritten, finalRelated⟩ := related.replace reference written replacement
    exact ⟨updated, coreWritten, finalRelated,
      AdministrativePreserved.write (List.mem_of_getElem? reference.mapped) coreWritten⟩
/-- The finite specialization is exactly the existing representation. No old
proof is weakened or replaced by the new interface. -/
theorem finiteHeap_iff {signatures : ProgramSignatures} {mapping : LocationMap} {world : Core.StoreTyping}
    {heap : Dynamic.Heap} {store : Core.Store} :
    HeapRepresents (finitePayload catalog signatures) mapping world heap store ↔
      DataHeap.HeapRepresents catalog signatures mapping world heap store := by
  constructor
  · intro related
    refine ⟨related.length_eq, related.injective, related.runtime_hasTypes, ?_⟩
    intro source target mapped
    obtain ⟨cell, value, payload, read, typed, found, represents⟩ := related.cells mapped
    exact ⟨cell, value, payload, read, typed, found, finiteCell_iff.mp represents⟩
  · intro related
    refine ⟨related.length_eq, related.injective, related.runtime_hasTypes, ?_⟩
    intro source target mapped
    obtain ⟨cell, value, payload, read, typed, found, represents⟩ := related.cells mapped
    exact ⟨cell, value, payload, read, typed, found, finiteCell_iff.mpr represents⟩

theorem HeapRepresents.fresh_unmapped {mapping : LocationMap} {world : Core.StoreTyping}
    {heap : Dynamic.Heap} {store : Core.Store} (related : HeapRepresents model mapping world heap store) :
    ∀ {source : Nat}, mapping[source]? ≠ some store.length := by
  intro source found
  have bound := related.target_lt found
  omega

/-- Environments need no additional payload model: their exact mapped
references and internal lexical slots already support every catalog type. -/
abbrev EnvRepresents (catalog : SourceCoreDataCatalog.Catalog) (mapping : LocationMap)
    (world : Core.StoreTyping) (administrativeContext : Core.Context := []) :=
  DataHeap.EnvRepresents catalog mapping world administrativeContext

theorem lookup_visible {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Core.Environment} {heap : Dynamic.Heap} {store : Core.Store}
    {id : Resolved.LocalId} {location : Dynamic.Location} {index : Nat} {payload : Core.Ty}
    (environments : EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents model mapping world heap store)
    (sourceLookup : Dynamic.Environment.LooksUp environment id location)
    (slot : SourceCoreLocalCell.lookup? scope id = some (index, payload)) :
    ∃ target cell value,
      canonical[index]? = some (.cellRef (Core.OptionalCell.cellType payload) target) ∧
      ReferenceRepresents mapping world location target payload ∧
      Dynamic.Heap.Reads heap location cell ∧ store.read? target = some value ∧
      CellRepresents model mapping world cell value payload := by
  obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible sourceLookup slot
  obtain ⟨cell, value, type, sourceRead, found, coreRead, represents⟩ := heaps.cells reference.mapped
  have same : type = payload := by
    simpa [Core.OptionalCell.cellType] using Option.some.inj (found.symm.trans reference.typed)
  subst type
  exact ⟨target, cell, value, coreLookup, reference, sourceRead, coreRead, represents⟩

theorem bind {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Core.Environment}
    {heap after : Dynamic.Heap} {store : Core.Store} {id : Resolved.LocalId}
    {sourceType : Ty} {sourceValue : Option Dynamic.Value} {location : Dynamic.Location}
    {value : Core.Value} {payload : Core.Ty}
    (environments : EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents model mapping world heap store)
    (cell : CellRepresents model mapping world ⟨sourceType, sourceValue, none⟩ value payload)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    EnvRepresents catalog (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      administrativeContext ((id, payload) :: scope) ((id, location) :: environment)
      (.cellRef (Core.OptionalCell.cellType payload) store.length :: canonical) ∧
    HeapRepresents model (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      after (store.allocate value).1 := by
  obtain ⟨heapRelated, reference⟩ := heaps.allocate cell allocated
  exact ⟨.cons reference (environments.extend ⟨_, rfl⟩ ⟨_, rfl⟩), heapRelated⟩

theorem bind_internal {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Core.Environment}
    {heap after : Dynamic.Heap} {store : Core.Store} {id : Resolved.LocalId}
    {sourceType : Ty} {sourceValue : Option Dynamic.Value} {location : Dynamic.Location}
    {value : Core.Value} {payload : Core.Ty}
    (environments : EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents model mapping world heap store)
    (fresh : scope.any (fun entry => decide (entry.1 = id)) = false)
    (cell : CellRepresents model mapping world ⟨sourceType, sourceValue, none⟩ value payload)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    EnvRepresents catalog (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      administrativeContext ((id, payload) :: scope) environment
      (.cellRef (Core.OptionalCell.cellType payload) store.length :: canonical) ∧
    HeapRepresents model (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      after (store.allocate value).1 := by
  obtain ⟨heapRelated, reference⟩ := heaps.allocate cell allocated
  exact ⟨.internal reference (environments.fresh_absent fresh)
    (environments.extend ⟨_, rfl⟩ ⟨_, rfl⟩), heapRelated⟩

end Solcore.SourceSemantics.CoreLowering.GenericHeap
