import Solcore.SourceSemantics.CoreLowering.GenericHeap

/-! Whole-cell models allow an ordinary value cell and a retained generalized
function descriptor to use different native payload types. Existing ordinary
heap relations embed without changing their projection or read properties. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericHeap
open Frontend Frontend.SourceInference TypeSystem GeneralHeap

structure CellModel (definitions : Core.DataEnvironment) where
  Represents : LocationMap → Core.StoreTyping → Dynamic.Cell → Core.Value → Core.Ty → Prop
  runtime_hasType : ∀ {mapping world cell value payload},
    Represents mapping world cell value payload →
      Core.RuntimeValueHasType world value (Core.OptionalCell.cellType payload) definitions
  extend : ∀ {mapping futureMapping world futureWorld cell value payload},
    Represents mapping world cell value payload →
    LocationMap.Extends mapping futureMapping → Core.WorldExtends world futureWorld →
    Represents futureMapping futureWorld cell value payload

def CellModel.ordinary {catalog : SourceCoreDataCatalog.Catalog}
    {projects : Projection} {definitions : Core.DataEnvironment}
    (payload : PayloadModel catalog projects definitions) : CellModel definitions where
  Represents := CellRepresents payload
  runtime_hasType := CellRepresents.runtime_hasType
  extend := CellRepresents.extend

structure CellHeapRepresents {definitions : Core.DataEnvironment}
    (model : CellModel definitions) (mapping : LocationMap) (world : Core.StoreTyping)
    (heap : Dynamic.Heap) (store : Core.Store) : Prop where
  length_eq : mapping.length = heap.cells.length
  injective : LocationMap.Injective mapping
  runtime_hasTypes : Core.RuntimeStoreHasTypes world store definitions
  cells : ∀ {source target : Nat}, mapping[source]? = some target →
    ∃ cell value payload,
      Dynamic.Heap.Reads heap ⟨source⟩ cell ∧
      world[target]? = some (Core.OptionalCell.cellType payload) ∧
      store.read? target = some value ∧ model.Represents mapping world cell value payload

theorem ordinaryHeap_iff {catalog : SourceCoreDataCatalog.Catalog}
    {projects : Projection} {definitions : Core.DataEnvironment}
    {model : PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store : Core.Store} :
    CellHeapRepresents (CellModel.ordinary model) mapping world heap store ↔
      HeapRepresents model mapping world heap store := by
  constructor
  · intro related
    exact ⟨related.length_eq, related.injective, related.runtime_hasTypes, related.cells⟩
  · intro related
    exact ⟨related.length_eq, related.injective, related.runtime_hasTypes, related.cells⟩

variable {definitions : Core.DataEnvironment} {model : CellModel definitions}

/-- Representation inclusion preserves the actual source heap, map and store.
This embeds an ordinary initial heap into a model that also has descriptors. -/
theorem CellHeapRepresents.includes {other : CellModel definitions}
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store : Core.Store}
    (included : ∀ {cell value payload}, model.Represents mapping world cell value payload →
      other.Represents mapping world cell value payload)
    (related : CellHeapRepresents model mapping world heap store) :
    CellHeapRepresents other mapping world heap store := by
  refine ⟨related.length_eq, related.injective, related.runtime_hasTypes, ?_⟩
  intro source target mapped
  obtain ⟨cell, value, payload, read, typed, found, represents⟩ := related.cells mapped
  exact ⟨cell, value, payload, read, typed, found, included represents⟩

private theorem cell_append_lookup {mapping : LocationMap} {fresh index target : Nat}
    (found : (mapping ++ [fresh])[index]? = some target) :
    mapping[index]? = some target ∨ (index = mapping.length ∧ target = fresh) := by
  by_cases old : index < mapping.length
  · left; rwa [List.getElem?_append_left old] at found
  · right
    have bound := (List.getElem?_eq_some_iff.mp found).1
    have same : index = mapping.length := by simp only [List.length_append, List.length_singleton] at bound; omega
    subst index
    exact ⟨rfl, by simpa using found.symm⟩

theorem CellHeapRepresents.empty : CellHeapRepresents model [] [] ⟨[]⟩ [] := by
  refine ⟨rfl, ?_, Core.RuntimeStoreHasTypes.nil definitions, ?_⟩
  · intro left right target impossible; simp at impossible
  · intro source target impossible; simp at impossible

theorem CellHeapRepresents.target_lt {mapping : LocationMap} {world : Core.StoreTyping}
    {heap : Dynamic.Heap} {store : Core.Store} (related : CellHeapRepresents model mapping world heap store)
    {source target : Nat} (mapped : mapping[source]? = some target) : target < store.length := by
  obtain ⟨_, _, _, _, typed, _, _⟩ := related.cells mapped
  exact related.runtime_hasTypes.location_lt typed

theorem CellHeapRepresents.read {mapping : LocationMap} {world : Core.StoreTyping}
    {heap : Dynamic.Heap} {store : Core.Store} (related : CellHeapRepresents model mapping world heap store)
    {location : Dynamic.Location} {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads heap location cell) :
    ∃ target value payload,
      ReferenceRepresents mapping world location target payload ∧
      store.read? target = some value ∧ model.Represents mapping world cell value payload := by
  have bound : location.index < mapping.length := by rw [related.length_eq]; exact read.location_valid
  have mapped := List.getElem?_eq_getElem bound
  obtain ⟨selected, value, payload, sourceRead, typed, coreRead, represents⟩ := related.cells mapped
  have same := read.functional sourceRead
  subst selected
  exact ⟨_, value, payload, ⟨mapped, typed⟩, coreRead, represents⟩

/-- Appending an administrative cell changes neither the source heap nor its
location map. Its payload can be a closure or reference; scalar store typing is
not required or derived. -/
theorem CellHeapRepresents.allocate_administrative
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store : Core.Store}
    (related : CellHeapRepresents model mapping world heap store) {value : Core.Value} {type : Core.Ty}
    (typed : Core.RuntimeValueHasType world value type definitions) :
    CellHeapRepresents model mapping (world ++ [type]) heap (store.allocate value).1 := by
  refine ⟨related.length_eq, related.injective, related.runtime_hasTypes.allocate typed, ?_⟩
  intro source target mapped
  obtain ⟨cell, old, payload, sourceRead, found, coreRead, represents⟩ := related.cells mapped
  exact ⟨cell, old, payload, sourceRead, (Core.WorldExtends.lookup ⟨[type], rfl⟩ found),
    (Core.Store.allocate_old_lookup store value (related.target_lt mapped)).trans coreRead,
    model.extend represents (.refl _) ⟨[type], rfl⟩⟩

/-- Append one authenticated source cell and its independently typed native
cell. Source and native locations use their respective heap lengths. -/
theorem CellHeapRepresents.append
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store : Core.Store}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (related : CellHeapRepresents model mapping world heap store)
    (represented : model.Represents mapping world cell value payload) :
    CellHeapRepresents model (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      ⟨heap.cells ++ [cell]⟩ (store.allocate value).1 ∧
    ReferenceRepresents (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      ⟨heap.cells.length⟩ store.length payload := by
  have extension : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
  have freshType : (world ++ [Core.OptionalCell.cellType payload])[store.length]? =
      some (Core.OptionalCell.cellType payload) := by rw [← related.runtime_hasTypes.length_eq]; simp
  have freshMap : (mapping ++ [store.length])[heap.cells.length]? = some store.length := by
    rw [← related.length_eq]; simp
  refine ⟨⟨?_, LocationMap.Injective.append related.injective store.length ?_,
    related.runtime_hasTypes.allocate (model.runtime_hasType represented), ?_⟩, ⟨freshMap, freshType⟩⟩
  · simp [related.length_eq]
  · intro index impossible
    have bound := related.target_lt impossible
    omega
  · intro source target mapped
    rcases cell_append_lookup mapped with old | ⟨sourceEq, targetEq⟩
    · obtain ⟨oldCell, oldValue, oldPayload, sourceRead, found, coreRead, represents⟩ := related.cells old
      cases sourceRead with
      | intro sourceAt =>
        exact ⟨oldCell, oldValue, oldPayload, .intro sourceAt.append_left,
          extension.lookup found,
          (Core.Store.allocate_old_lookup store value (related.target_lt old)).trans coreRead,
          model.extend represents ⟨[store.length], rfl⟩ extension⟩
    · subst target
      rw [related.length_eq] at sourceEq
      subst source
      exact ⟨cell, value, payload, .intro (Dynamic.Heap.CellAt.append_last _ _), freshType,
        Core.Store.allocate_fresh_lookup store value,
        model.extend represented ⟨[store.length], rfl⟩ extension⟩

theorem CellHeapRepresents.allocate_ordinary
    {mapping : LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap} {store : Core.Store}
    {type : Ty} {sourceValue : Option Dynamic.Value} {location : Dynamic.Location}
    {value : Core.Value} {payload : Core.Ty}
    (related : CellHeapRepresents model mapping world heap store)
    (cell : model.Represents mapping world { type, value := sourceValue } value payload)
    (allocated : Dynamic.Heap.Allocates heap type sourceValue location after) :
    CellHeapRepresents model (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      after (store.allocate value).1 ∧
    ReferenceRepresents (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      location store.length payload := by
  cases allocated
  exact related.append cell

theorem CellHeapRepresents.allocate_generalized
    {mapping : LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap} {store : Core.Store}
    {function : Dynamic.GeneralizedClosure} {location : Dynamic.Location}
    {value : Core.Value} {payload : Core.Ty}
    (related : CellHeapRepresents model mapping world heap store)
    (cell : model.Represents mapping world
      ⟨function.binder.scheme.body, none, some function⟩ value payload)
    (allocated : Dynamic.Heap.AllocatesGeneralized heap function location after) :
    CellHeapRepresents model (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      after (store.allocate value).1 ∧
    ReferenceRepresents (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      location store.length payload := by
  cases allocated
  exact related.append cell

/-- A well-typed write to an unmapped administrative cell preserves the source
heap and every source-visible cell. This permits installing recursive closures
after allocating their optional administrative function cells. -/
theorem CellHeapRepresents.write_administrative
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap}
    {store updated : Core.Store} {location : Core.Location} {type : Core.Ty} {value : Core.Value}
    (related : CellHeapRepresents model mapping world heap store)
    (absent : ∀ {source : Nat}, mapping[source]? ≠ some location)
    (found : world[location]? = some type) (typed : Core.RuntimeValueHasType world value type definitions)
    (written : store.write? location value = some updated) :
    CellHeapRepresents model mapping world heap updated := by
  refine ⟨related.length_eq, related.injective, related.runtime_hasTypes.write found typed written, ?_⟩
  intro source target mapped
  obtain ⟨cell, stored, payload, sourceRead, typed, coreRead, represents⟩ := related.cells mapped
  have different : target ≠ location := by intro same; exact absent (same ▸ mapped)
  exact ⟨cell, stored, payload, sourceRead, typed,
    (Core.Store.write?_preserves_other written different).trans coreRead, represents⟩

/-- Structural replacement changes only the mapped Core location. Map
injectivity is what prevents a write from changing a distinct source cell. -/
theorem CellHeapRepresents.replace
    {mapping : LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap} {store : Core.Store}
    {location : Dynamic.Location} {target : Core.Location} {payload : Core.Ty}
    {replacement : Dynamic.Cell} {value : Core.Value}
    (related : CellHeapRepresents model mapping world heap store)
    (reference : ReferenceRepresents mapping world location target payload)
    (written : Dynamic.Heap.CellsWrite heap.cells location.index replacement after.cells)
    (newCell : model.Represents mapping world replacement value payload) :
    ∃ updated, store.write? target value = some updated ∧
      CellHeapRepresents model mapping world after updated := by
  obtain ⟨updated, coreWritten⟩ := related.runtime_hasTypes.write_exists (value := value) reference.typed
  refine ⟨updated, coreWritten, ⟨related.length_eq.trans written.length_eq.symm,
    related.injective, related.runtime_hasTypes.write reference.typed
      (model.runtime_hasType newCell) coreWritten, ?_⟩⟩
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

variable {catalog : SourceCoreDataCatalog.Catalog}

theorem CellHeapRepresents.lookup_visible {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Core.Environment} {heap : Dynamic.Heap} {store : Core.Store}
    {id : Resolved.LocalId} {location : Dynamic.Location} {index : Nat} {payload : Core.Ty}
    (environments : EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : CellHeapRepresents model mapping world heap store)
    (sourceLookup : Dynamic.Environment.LooksUp environment id location)
    (slot : SourceCoreLocalCell.lookup? scope id = some (index, payload)) :
    ∃ target cell value,
      canonical[index]? = some (.cellRef (Core.OptionalCell.cellType payload) target) ∧
      ReferenceRepresents mapping world location target payload ∧
      Dynamic.Heap.Reads heap location cell ∧ store.read? target = some value ∧
      model.Represents mapping world cell value payload := by
  obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible sourceLookup slot
  obtain ⟨cell, value, type, sourceRead, found, coreRead, represents⟩ := heaps.cells reference.mapped
  have same : type = payload := by
    simpa [Core.OptionalCell.cellType] using Option.some.inj (found.symm.trans reference.typed)
  subst type
  exact ⟨target, cell, value, coreLookup, reference, sourceRead, coreRead, represents⟩

end Solcore.SourceSemantics.CoreLowering.GenericHeap
