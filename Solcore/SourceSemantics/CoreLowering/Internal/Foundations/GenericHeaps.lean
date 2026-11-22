import Solcore.SourceSemantics.CoreLowering.Internal.Data.HeapsAndBindings

/-!
# Generic heaps

`GenericHeap`, the location maps, worlds and administrative frames of ordinary source cells, and `GenericCellHeap`, the same over whole cells, with the payload heap.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericHeapPayload
/-! An interface for authenticated ordinary cell payload relations. Models may
refer to the finite location map and runtime typing world, so a captured source
location can correspond to a Core reference without recursively traversing a
cyclic store. These laws establish representation typing and extension only.
A function model still needs explicit source identity/code authentication and
call semantics; a mapping model still needs entry and comparison semantics.
-/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericHeap
open Frontend Frontend.SourceInference GeneralHeap

/-- A projection relation can describe a different native carrier while the
catalog supplies only the registered Core definitions. The default preserves
all existing strict-catalog APIs. -/
abbrev Projection := TypeSystem.Ty → Core.Ty → Prop

abbrev strictProjection (catalog : SourceCoreDataCatalog.Catalog) : Projection :=
  fun source payload => catalog.project source = .ok payload

structure PayloadModel (catalog : SourceCoreDataCatalog.Catalog)
    (projects : Projection := strictProjection catalog)
    (definitions : Core.DataEnvironment := catalog.definitions) where
  Represents : LocationMap → Core.StoreTyping → TypeSystem.Ty → Dynamic.Value → Core.Value → Core.Ty → Prop
  projection : ∀ {mapping world sourceType sourceValue value payload},
    Represents mapping world sourceType sourceValue value payload → projects sourceType payload
  runtime_hasType : ∀ {mapping world sourceType sourceValue value payload},
    Represents mapping world sourceType sourceValue value payload →
      Core.RuntimeValueHasType world value payload definitions
  extend : ∀ {mapping futureMapping world futureWorld sourceType sourceValue value payload},
    Represents mapping world sourceType sourceValue value payload →
    LocationMap.Extends mapping futureMapping → Core.WorldExtends world futureWorld →
    Represents futureMapping futureWorld sourceType sourceValue value payload

/-- Optional ordinary cells preserve the source declaration's type and reject
retained generalized-cell metadata. Their payload representation is supplied
by the model, not inferred from Core runtime typing. -/
inductive CellRepresents {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection} {definitions : Core.DataEnvironment}
    (model : PayloadModel catalog projects definitions)
    (mapping : LocationMap) (world : Core.StoreTyping) : Dynamic.Cell → Core.Value → Core.Ty → Prop where
  | uninitialized {sourceType : TypeSystem.Ty} {payload : Core.Ty}
      (projection : projects sourceType payload) :
      CellRepresents model mapping world ⟨sourceType, none, none⟩ (.inLeft payload .unit) payload
  | initialized {sourceType : TypeSystem.Ty} {payload : Core.Ty} {source : Dynamic.Value} {value : Core.Value}
      (represented : model.Represents mapping world sourceType source value payload) :
      CellRepresents model mapping world ⟨sourceType, some source, none⟩ (.inRight .unit value) payload

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection} {definitions : Core.DataEnvironment}
  {model : PayloadModel catalog projects definitions}

theorem CellRepresents.projection {mapping : LocationMap} {world : Core.StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (represented : CellRepresents model mapping world cell value payload) : projects cell.type payload := by
  cases represented with
  | uninitialized projection => exact projection
  | initialized related => exact model.projection related

theorem CellRepresents.ordinary {mapping : LocationMap} {world : Core.StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (represented : CellRepresents model mapping world cell value payload) : cell.generalized = none := by
  cases represented <;> rfl

theorem CellRepresents.runtime_hasType {mapping : LocationMap} {world : Core.StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (represented : CellRepresents model mapping world cell value payload) :
    Core.RuntimeValueHasType world value (Core.OptionalCell.cellType payload) definitions := by
  cases represented with
  | uninitialized => exact .inLeft .unit
  | initialized related => exact .inRight (model.runtime_hasType related)

theorem CellRepresents.extend {mapping futureMapping : LocationMap} {world futureWorld : Core.StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (represented : CellRepresents model mapping world cell value payload)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : Core.WorldExtends world futureWorld) :
    CellRepresents model futureMapping futureWorld cell value payload := by
  cases represented with
  | uninitialized projection => exact .uninitialized projection
  | initialized related => exact .initialized (model.extend related maps worlds)

/-- The previously proved finite unit/Bool/Word/Integer/product/nominal model.
The extra explicit projection records the payload type chosen for this cell. -/
def finitePayload (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures) : PayloadModel catalog where
  Represents := fun _ _ sourceType source value payload =>
    catalog.project sourceType = .ok payload ∧
      DataPatternTypedValues.TypedValueRep catalog signatures sourceType source value
  projection := fun related => related.1
  runtime_hasType := by
    intro mapping world sourceType source value payload related
    obtain ⟨type, projection, typed⟩ := DataValueTyping.TypedValueRep.project_typed related.2
    have same := Except.ok.inj (projection.symm.trans related.1)
    exact same ▸ typed world
  extend := fun related _ _ => related

theorem finiteCell_iff {signatures : ProgramSignatures} {mapping : LocationMap} {world : Core.StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty} :
    CellRepresents (finitePayload catalog signatures) mapping world cell value payload ↔
      DataHeap.CellRepresents catalog signatures cell value payload := by
  constructor
  · intro represented
    cases represented with
    | uninitialized projection => exact .uninitialized projection
    | initialized related => exact .initialized related.1 related.2
  · intro represented
    cases represented with
    | uninitialized projection => exact .uninitialized projection
    | initialized projection related => exact .initialized ⟨projection, related⟩

end Solcore.SourceSemantics.CoreLowering.GenericHeap
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericHeap
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

structure HeapRepresents {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection} {definitions : Core.DataEnvironment} (model : PayloadModel catalog projects definitions) (mapping : LocationMap) (world : Core.StoreTyping)
    (heap : Dynamic.Heap) (store : Core.Store) : Prop where
  length_eq : mapping.length = heap.cells.length
  injective : LocationMap.Injective mapping
  runtime_hasTypes : Core.RuntimeStoreHasTypes world store definitions
  cells : ∀ {source target : Nat}, mapping[source]? = some target →
    ∃ cell value payload,
      Dynamic.Heap.Reads heap ⟨source⟩ cell ∧
      world[target]? = some (Core.OptionalCell.cellType payload) ∧
      store.read? target = some value ∧ CellRepresents model mapping world cell value payload

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection} {definitions : Core.DataEnvironment}
  {model : PayloadModel catalog projects definitions}

theorem HeapRepresents.empty : HeapRepresents model [] [] ⟨[]⟩ [] := by
  refine ⟨rfl, ?_, Core.RuntimeStoreHasTypes.nil definitions, ?_⟩
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
    (typed : Core.RuntimeValueHasType world value type definitions) :
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

/-- A copy of any source cell, generalized principal included, is a mapped
allocation like `HeapRepresents.allocate`. -/
theorem HeapRepresents.allocate_copy
    {mapping : LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap} {store : Core.Store}
    {copied : Dynamic.Cell} {location : Dynamic.Location}
    {value : Core.Value} {payload : Core.Ty}
    (related : HeapRepresents model mapping world heap store)
    (cell : CellRepresents model mapping world copied value payload)
    (allocated : Dynamic.Heap.AllocatesCopy heap copied location after) :
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
      exact ⟨oldCell, oldValue, oldPayload, Dynamic.Heap.AllocatesCopy.preserves_read .append sourceRead,
        extension.lookup found,
        (Core.Store.allocate_old_lookup store value (related.target_lt old)).trans coreRead,
        represents.extend ⟨[store.length], rfl⟩ extension⟩
    · subst target
      rw [related.length_eq] at sourceEq
      subst source
      exact ⟨_, value, payload, Dynamic.Heap.AllocatesCopy.reads_new .append, freshType,
        Core.Store.allocate_fresh_lookup store value, cell.extend ⟨[store.length], rfl⟩ extension⟩

/-- A well-typed write to an unmapped administrative cell preserves the source
heap and every source-visible cell. This permits installing recursive closures
after allocating their optional administrative function cells. -/
theorem HeapRepresents.write_administrative
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap}
    {store updated : Core.Store} {location : Core.Location} {type : Core.Ty} {value : Core.Value}
    (related : HeapRepresents model mapping world heap store)
    (absent : ∀ {source : Nat}, mapping[source]? ≠ some location)
    (found : world[location]? = some type) (typed : Core.RuntimeValueHasType world value type definitions)
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
    (world : Core.StoreTyping) (administrativeContext : Core.Context := [])
    (scope : SourceCoreLocalCell.Scope) (environment : Dynamic.Environment) (canonical : Core.Environment)
    (definitions : Core.DataEnvironment := catalog.definitions) :=
  DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions

theorem lookup_visible {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Core.Environment} {heap : Dynamic.Heap} {store : Core.Store}
    {id : Resolved.LocalId} {location : Dynamic.Location} {index : Nat} {payload : Core.Ty}
    (environments : EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
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
    (environments : EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : HeapRepresents model mapping world heap store)
    (cell : CellRepresents model mapping world ⟨sourceType, sourceValue, none⟩ value payload)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    EnvRepresents catalog (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      administrativeContext ((id, payload) :: scope) ((id, location) :: environment)
      (.cellRef (Core.OptionalCell.cellType payload) store.length :: canonical) definitions ∧
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
    (environments : EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : HeapRepresents model mapping world heap store)
    (fresh : scope.any (fun entry => decide (entry.1 = id)) = false)
    (cell : CellRepresents model mapping world ⟨sourceType, sourceValue, none⟩ value payload)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    EnvRepresents catalog (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      administrativeContext ((id, payload) :: scope) environment
      (.cellRef (Core.OptionalCell.cellType payload) store.length :: canonical) definitions ∧
    HeapRepresents model (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      after (store.allocate value).1 := by
  obtain ⟨heapRelated, reference⟩ := heaps.allocate cell allocated
  exact ⟨.internal reference.typed (environments.fresh_absent fresh)
    (environments.extend ⟨_, rfl⟩ ⟨_, rfl⟩), heapRelated⟩

end Solcore.SourceSemantics.CoreLowering.GenericHeap
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericCellHeap
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
  /-- The cells of array objects, beside the optional cells: an array's Core cell holds its contents at a
  product type. A model that keeps the default has none. -/
  Array : LocationMap → Core.StoreTyping → Dynamic.Cell → Core.Value → Core.Ty → Prop :=
    fun _ _ _ _ _ => False
  array_runtime_hasType : ∀ {mapping world cell value type},
      Array mapping world cell value type → Core.RuntimeValueHasType world value type definitions := by
    intro _ _ _ _ _ impossible; exact False.elim impossible
  array_extend : ∀ {mapping futureMapping world futureWorld cell value type},
      Array mapping world cell value type →
      LocationMap.Extends mapping futureMapping → Core.WorldExtends world futureWorld →
      Array futureMapping futureWorld cell value type := by
    intro _ _ _ _ _ _ _ impossible; exact False.elim impossible
  /-- An array cell holds an array object, and its Core type is a product, never an optional cell's. -/
  array_shape : ∀ {mapping world cell value type}, Array mapping world cell value type →
      (∃ element elements, cell = ⟨.arrayObject element, some (.arrayObject element elements), none⟩) ∧
        ∃ left right, type = .product left right := by
    intro _ _ _ _ _ impossible; exact False.elim impossible

def CellModel.ordinary {catalog : SourceCoreDataCatalog.Catalog}
    {projects : Projection} {definitions : Core.DataEnvironment}
    (payload : PayloadModel catalog projects definitions) : CellModel definitions where
  Represents := CellRepresents payload
  runtime_hasType := CellRepresents.runtime_hasType
  extend := CellRepresents.extend

/-- How a mapped Source cell stands for the Core cell at `target`: an optional cell of the model, or an
array object's cell. -/
inductive CellAt {definitions : Core.DataEnvironment} (model : CellModel definitions) (mapping : LocationMap)
    (world : Core.StoreTyping) (target : Nat) (cell : Dynamic.Cell) (value : Core.Value) : Prop where
  | optional {payload : Core.Ty} (typed : world[target]? = some (Core.OptionalCell.cellType payload))
      (represented : model.Represents mapping world cell value payload)
  | array {type : Core.Ty} (typed : world[target]? = some type)
      (represented : model.Array mapping world cell value type)

structure CellHeapRepresents {definitions : Core.DataEnvironment}
    (model : CellModel definitions) (mapping : LocationMap) (world : Core.StoreTyping)
    (heap : Dynamic.Heap) (store : Core.Store) : Prop where
  length_eq : mapping.length = heap.cells.length
  injective : LocationMap.Injective mapping
  runtime_hasTypes : Core.RuntimeStoreHasTypes world store definitions
  cells : ∀ {source target : Nat}, mapping[source]? = some target →
    ∃ cell value,
      Dynamic.Heap.Reads heap ⟨source⟩ cell ∧ store.read? target = some value ∧
      CellAt model mapping world target cell value

section CellAt
variable {definitions : Core.DataEnvironment} {model : CellModel definitions}
  {mapping : LocationMap} {world : Core.StoreTyping} {target : Nat} {cell : Dynamic.Cell} {value : Core.Value}

theorem CellAt.typed (stands : CellAt model mapping world target cell value) : ∃ type, world[target]? = some type := by
  cases stands with
  | optional typed => exact ⟨_, typed⟩
  | array typed => exact ⟨_, typed⟩

theorem CellAt.runtime_hasType (stands : CellAt model mapping world target cell value) :
    ∃ type, world[target]? = some type ∧ Core.RuntimeValueHasType world value type definitions := by
  cases stands with
  | optional typed represented => exact ⟨_, typed, model.runtime_hasType represented⟩
  | array typed represented => exact ⟨_, typed, model.array_runtime_hasType represented⟩

theorem CellAt.extend {futureMapping : LocationMap} {futureWorld : Core.StoreTyping}
    (stands : CellAt model mapping world target cell value)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : Core.WorldExtends world futureWorld) :
    CellAt model futureMapping futureWorld target cell value := by
  cases stands with
  | optional typed represented => exact .optional (worlds.lookup typed) (model.extend represented maps worlds)
  | array typed represented => exact .array (worlds.lookup typed) (model.array_extend represented maps worlds)

/-- A Core cell typed as an optional cell is the model's optional cell, never an array's. -/
theorem CellAt.optional_of_typed {payload : Core.Ty} (stands : CellAt model mapping world target cell value)
    (typed : world[target]? = some (Core.OptionalCell.cellType payload)) :
    model.Represents mapping world cell value payload := by
  cases stands with
  | optional found represented =>
      have same : Core.OptionalCell.cellType _ = Core.OptionalCell.cellType payload :=
        Option.some.inj (found.symm.trans typed)
      simp only [Core.OptionalCell.cellType, Core.Ty.sum.injEq, true_and] at same
      subst same
      exact represented
  | array found represented =>
      obtain ⟨_, left, right, product⟩ := model.array_shape represented
      have same := Option.some.inj (found.symm.trans typed)
      rw [product] at same
      cases same

/-- A cell that holds no array object is the model's optional cell. -/
theorem CellAt.optional_of_cell (stands : CellAt model mapping world target cell value)
    (notArray : ∀ element elements, cell ≠ ⟨.arrayObject element, some (.arrayObject element elements), none⟩) :
    ∃ payload, world[target]? = some (Core.OptionalCell.cellType payload) ∧
      model.Represents mapping world cell value payload := by
  cases stands with
  | optional typed represented => exact ⟨_, typed, represented⟩
  | array _ represented =>
      obtain ⟨⟨element, elements, same⟩, _⟩ := model.array_shape represented
      exact (notArray element elements same).elim

end CellAt

theorem ordinaryHeap_iff {catalog : SourceCoreDataCatalog.Catalog}
    {projects : Projection} {definitions : Core.DataEnvironment}
    {model : PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store : Core.Store} :
    CellHeapRepresents (CellModel.ordinary model) mapping world heap store ↔
      HeapRepresents model mapping world heap store := by
  constructor
  · intro related
    refine ⟨related.length_eq, related.injective, related.runtime_hasTypes, ?_⟩
    intro source target mapped
    obtain ⟨cell, value, read, found, stands⟩ := related.cells mapped
    cases stands with
    | optional typed represents => exact ⟨cell, value, _, read, typed, found, represents⟩
    | array _ impossible => exact False.elim impossible
  · intro related
    refine ⟨related.length_eq, related.injective, related.runtime_hasTypes, ?_⟩
    intro source target mapped
    obtain ⟨cell, value, payload, read, typed, found, represents⟩ := related.cells mapped
    exact ⟨cell, value, read, found, .optional typed represents⟩

variable {definitions : Core.DataEnvironment} {model : CellModel definitions}

/-- A mapped cell whose Core cell is typed as an optional cell is the model's optional cell. -/
theorem CellHeapRepresents.referenced {mapping : LocationMap} {world : Core.StoreTyping}
    {heap : Dynamic.Heap} {store : Core.Store} (related : CellHeapRepresents model mapping world heap store)
    {source target : Nat} {payload : Core.Ty} (mapped : mapping[source]? = some target)
    (typed : world[target]? = some (Core.OptionalCell.cellType payload)) :
    ∃ cell value payload,
      Dynamic.Heap.Reads heap ⟨source⟩ cell ∧
      world[target]? = some (Core.OptionalCell.cellType payload) ∧
      store.read? target = some value ∧ model.Represents mapping world cell value payload := by
  obtain ⟨cell, value, read, found, stands⟩ := related.cells mapped
  exact ⟨cell, value, payload, read, typed, found, stands.optional_of_typed typed⟩

/-- Representation inclusion preserves the actual source heap, map and store.
This embeds an ordinary initial heap into a model that also has descriptors. -/
theorem CellHeapRepresents.includes {other : CellModel definitions}
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store : Core.Store}
    (included : ∀ {cell value payload}, model.Represents mapping world cell value payload →
      other.Represents mapping world cell value payload)
    (related : CellHeapRepresents model mapping world heap store)
    (arrays : ∀ {cell value type}, model.Array mapping world cell value type →
      other.Array mapping world cell value type := by
      intro _ _ _ represented; first | exact represented | exact False.elim represented) :
    CellHeapRepresents other mapping world heap store := by
  refine ⟨related.length_eq, related.injective, related.runtime_hasTypes, ?_⟩
  intro source target mapped
  obtain ⟨cell, value, read, found, stands⟩ := related.cells mapped
  cases stands with
  | optional typed represents => exact ⟨cell, value, read, found, .optional typed (included represents)⟩
  | array typed represents => exact ⟨cell, value, read, found, .array typed (arrays represents)⟩

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
  obtain ⟨_, _, _, _, stands⟩ := related.cells mapped
  obtain ⟨_, typed⟩ := stands.typed
  exact related.runtime_hasTypes.location_lt typed

/-- A cell read that holds no array object is the model's optional cell at its Core reference. -/
theorem CellHeapRepresents.read {mapping : LocationMap} {world : Core.StoreTyping}
    {heap : Dynamic.Heap} {store : Core.Store} (related : CellHeapRepresents model mapping world heap store)
    {location : Dynamic.Location} {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads heap location cell)
    (notArray : ∀ element elements, cell ≠ ⟨.arrayObject element, some (.arrayObject element elements), none⟩) :
    ∃ target value payload,
      ReferenceRepresents mapping world location target payload ∧
      store.read? target = some value ∧ model.Represents mapping world cell value payload := by
  have bound : location.index < mapping.length := by rw [related.length_eq]; exact read.location_valid
  have mapped := List.getElem?_eq_getElem bound
  obtain ⟨selected, value, sourceRead, coreRead, stands⟩ := related.cells mapped
  have same := read.functional sourceRead
  subst selected
  obtain ⟨payload, typed, represents⟩ := stands.optional_of_cell notArray
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
  obtain ⟨cell, old, sourceRead, coreRead, stands⟩ := related.cells mapped
  exact ⟨cell, old, sourceRead,
    (Core.Store.allocate_old_lookup store value (related.target_lt mapped)).trans coreRead,
    stands.extend (.refl _) ⟨[type], rfl⟩⟩

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
    · obtain ⟨oldCell, oldValue, sourceRead, coreRead, stands⟩ := related.cells old
      cases sourceRead with
      | intro sourceAt =>
        exact ⟨oldCell, oldValue, .intro sourceAt.append_left,
          (Core.Store.allocate_old_lookup store value (related.target_lt old)).trans coreRead,
          stands.extend ⟨[store.length], rfl⟩ extension⟩
    · subst target
      rw [related.length_eq] at sourceEq
      subst source
      exact ⟨cell, value, .intro (Dynamic.Heap.CellAt.append_last _ _),
        Core.Store.allocate_fresh_lookup store value,
        .optional freshType (model.extend represented ⟨[store.length], rfl⟩ extension)⟩

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
  obtain ⟨cell, stored, sourceRead, coreRead, stands⟩ := related.cells mapped
  have different : target ≠ location := by intro same; exact absent (same ▸ mapped)
  exact ⟨cell, stored, sourceRead,
    (Core.Store.write?_preserves_other written different).trans coreRead, stands⟩

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
  obtain ⟨cell, stored, sourceRead, coreRead, stands⟩ := related.cells mapped
  by_cases same : source = location.index
  · subst source
    have targetEq : other = target := Option.some.inj (mapped.symm.trans reference.mapped)
    subst other
    exact ⟨replacement, value, .intro written.reads_replacement,
      Core.Store.write?_reads_written coreWritten, .optional reference.typed newCell⟩
  · have different : other ≠ target := by
      intro equal
      exact same (related.injective (equal ▸ mapped) reference.mapped)
    cases sourceRead with
    | intro sourceAt =>
        exact ⟨cell, stored, .intro (written.preserves_other same sourceAt),
          (Core.Store.write?_preserves_other coreWritten different).trans coreRead, stands⟩

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
  obtain ⟨cell, value, type, sourceRead, found, coreRead, represents⟩ :=
    heaps.referenced reference.mapped reference.typed
  have same : type = payload := by
    simpa [Core.OptionalCell.cellType] using Option.some.inj (found.symm.trans reference.typed)
  subst type
  exact ⟨target, cell, value, coreLookup, reference, sourceRead, coreRead, represents⟩

end Solcore.SourceSemantics.CoreLowering.GenericHeap
end

section
/-! Array objects' cells. An array object's Core cell holds the word of its length, a default element and
an ordered mapping from the words of positions to the elements present. The payload model represents each
element at the element type; a position without an entry reads the default. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericHeap
open Frontend Frontend.SourceInference TypeSystem GeneralHeap

/-- The equality an array's entries are looked up by. -/
abbrev arrayKeyEqual : Core.OrderedMapping.Predicate := fun left right => decide (left = right)

/-- The layout of an array's present elements, keyed by words. -/
abbrev arrayLayout (payload : Core.Ty) (identity : Core.DataTypeId) : Core.OrderedMapping.Layout :=
  ⟨.word, payload, identity⟩

/-- The Core value an array holds at `position`: its entry, or the default element. -/
def arrayEntry (entries : Core.OrderedMapping.Entries) (default : Core.Value) (position : Nat) : Core.Value :=
  (Core.OrderedMapping.lookupEntries arrayKeyEqual (.word (Core.Word.ofNatModulo position)) entries).getD default

/-- An array cell's contents: the Source `elements` at `element`, and on the Core side a default and
entries at `payload`, keyed by the words of positions below the length. -/
structure ArrayContents {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection}
    {definitions : Core.DataEnvironment} (model : PayloadModel catalog projects definitions)
    (mapping : LocationMap) (world : Core.StoreTyping) (element : Ty) (elements : List Dynamic.Value)
    (payload : Core.Ty) (identity : Core.DataTypeId) (default : Core.Value)
    (entries : Core.OrderedMapping.Entries) : Prop where
  projection : projects element payload
  registered : (arrayLayout payload identity).Registered definitions
  bounded : elements.length < Core.wordModulus
  default_typed : Core.RuntimeValueHasType world default payload definitions
  keys : ∀ key value, (key, value) ∈ entries →
    ∃ position, position < elements.length ∧ key = .word (Core.Word.ofNatModulo position)
  entries_typed : ∀ key value, (key, value) ∈ entries →
    Core.RuntimeValueHasType world value payload definitions
  represented : ∀ position (below : position < elements.length),
    model.Represents mapping world element elements[position] (arrayEntry entries default position) payload

/-- An array object's cell and its Core cell `(n, (d, entries))`, where `n` is the length's word. -/
def ArrayCellRepresents {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection}
    {definitions : Core.DataEnvironment} (model : PayloadModel catalog projects definitions)
    (mapping : LocationMap) (world : Core.StoreTyping) (cell : Dynamic.Cell) (value : Core.Value)
    (type : Core.Ty) : Prop :=
  ∃ element elements payload identity default entries,
    cell = ⟨.arrayObject element, some (.arrayObject element elements), none⟩ ∧
    value = .pair (.word (Core.Word.ofNatModulo elements.length))
      (.pair default (Core.OrderedMapping.encode (arrayLayout payload identity) entries)) ∧
    type = .product .word (.product payload (.namedData identity)) ∧
    ArrayContents model mapping world element elements payload identity default entries

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection} {definitions : Core.DataEnvironment}
  {model : PayloadModel catalog projects definitions}

theorem ArrayContents.encode_typed {mapping : LocationMap} {world : Core.StoreTyping} {element : Ty}
    {elements : List Dynamic.Value} {payload : Core.Ty} {identity : Core.DataTypeId} {default : Core.Value}
    {entries : Core.OrderedMapping.Entries}
    (contents : ArrayContents model mapping world element elements payload identity default entries) :
    Core.RuntimeValueHasType world (Core.OrderedMapping.encode (arrayLayout payload identity) entries)
      (.namedData identity) definitions :=
  Core.OrderedMapping.encode_hasType contents.registered entries fun key value member => by
    obtain ⟨_, _, same⟩ := contents.keys key value member
    refine ⟨?_, contents.entries_typed key value member⟩
    rw [same]
    exact .word

theorem ArrayContents.extend {mapping futureMapping : LocationMap} {world futureWorld : Core.StoreTyping}
    {element : Ty} {elements : List Dynamic.Value} {payload : Core.Ty} {identity : Core.DataTypeId}
    {default : Core.Value} {entries : Core.OrderedMapping.Entries}
    (contents : ArrayContents model mapping world element elements payload identity default entries)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : Core.WorldExtends world futureWorld) :
    ArrayContents model futureMapping futureWorld element elements payload identity default entries where
  projection := contents.projection
  registered := contents.registered
  bounded := contents.bounded
  default_typed := contents.default_typed.weaken worlds
  keys := contents.keys
  entries_typed := fun key value member => (contents.entries_typed key value member).weaken worlds
  represented := fun position below => model.extend (contents.represented position below) maps worlds

theorem ArrayCellRepresents.runtime_hasType {mapping : LocationMap} {world : Core.StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {type : Core.Ty}
    (represented : ArrayCellRepresents model mapping world cell value type) :
    Core.RuntimeValueHasType world value type definitions := by
  obtain ⟨_, _, _, _, _, _, _, rfl, rfl, contents⟩ := represented
  exact .pair .word (.pair contents.default_typed contents.encode_typed)

theorem ArrayCellRepresents.extend {mapping futureMapping : LocationMap} {world futureWorld : Core.StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {type : Core.Ty}
    (represented : ArrayCellRepresents model mapping world cell value type)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : Core.WorldExtends world futureWorld) :
    ArrayCellRepresents model futureMapping futureWorld cell value type := by
  obtain ⟨element, elements, payload, identity, default, entries, cellEq, valueEq, typeEq, contents⟩ := represented
  exact ⟨element, elements, payload, identity, default, entries, cellEq, valueEq, typeEq, contents.extend maps worlds⟩

theorem ArrayCellRepresents.shape {mapping : LocationMap} {world : Core.StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {type : Core.Ty}
    (represented : ArrayCellRepresents model mapping world cell value type) :
    (∃ element elements, cell = ⟨.arrayObject element, some (.arrayObject element elements), none⟩) ∧
      ∃ left right, type = .product left right := by
  obtain ⟨element, elements, _, _, _, _, cellEq, _, typeEq, _⟩ := represented
  exact ⟨⟨element, elements, cellEq⟩, _, _, typeEq⟩

/-- The insert finds the position it wrote. -/
theorem lookupEntries_insert_same (key value : Core.Value) (entries : Core.OrderedMapping.Entries) :
    Core.OrderedMapping.lookupEntries arrayKeyEqual key
      (Core.OrderedMapping.insertEntries arrayKeyEqual key value entries) = some value := by
  induction entries with
  | nil => simp [Core.OrderedMapping.insertEntries, Core.OrderedMapping.lookupEntries]
  | cons entry rest ih =>
      obtain ⟨stored, old⟩ := entry
      by_cases same : key = stored
      · subst same
        simp [Core.OrderedMapping.insertEntries, Core.OrderedMapping.lookupEntries]
      · simp [Core.OrderedMapping.insertEntries, Core.OrderedMapping.lookupEntries, same, ih]

/-- The insert leaves every other position as it was. -/
theorem lookupEntries_insert_other {key other : Core.Value} (different : other ≠ key) (value : Core.Value)
    (entries : Core.OrderedMapping.Entries) :
    Core.OrderedMapping.lookupEntries arrayKeyEqual other
        (Core.OrderedMapping.insertEntries arrayKeyEqual key value entries) =
      Core.OrderedMapping.lookupEntries arrayKeyEqual other entries := by
  induction entries with
  | nil => simp [Core.OrderedMapping.insertEntries, Core.OrderedMapping.lookupEntries, different]
  | cons entry rest ih =>
      obtain ⟨stored, old⟩ := entry
      by_cases same : key = stored
      · subst same
        simp [Core.OrderedMapping.insertEntries, Core.OrderedMapping.lookupEntries, different]
      · by_cases found : other = stored
        · subst found
          simp [Core.OrderedMapping.insertEntries, Core.OrderedMapping.lookupEntries, same]
        · simp [Core.OrderedMapping.insertEntries, Core.OrderedMapping.lookupEntries, same, found, ih]

theorem mem_insertEntries {key value stored storedValue : Core.Value} {entries : Core.OrderedMapping.Entries}
    (member : (stored, storedValue) ∈ Core.OrderedMapping.insertEntries arrayKeyEqual key value entries) :
    (stored, storedValue) ∈ entries ∨ (stored = key ∧ storedValue = value) := by
  induction entries with
  | nil =>
      simp only [Core.OrderedMapping.insertEntries, List.mem_singleton, Prod.mk.injEq] at member
      exact .inr member
  | cons entry rest ih =>
      obtain ⟨first, firstValue⟩ := entry
      by_cases same : key = first
      · subst same
        simp only [Core.OrderedMapping.insertEntries, arrayKeyEqual, decide_true, ↓reduceIte,
          List.mem_cons, Prod.mk.injEq] at member
        rcases member with ⟨rfl, rfl⟩ | inRest
        · exact .inr ⟨rfl, rfl⟩
        · exact .inl (List.mem_cons_of_mem _ inRest)
      · simp only [Core.OrderedMapping.insertEntries, arrayKeyEqual, same, decide_false,
          Bool.false_eq_true, ↓reduceIte, List.mem_cons, Prod.mk.injEq] at member
        rcases member with ⟨rfl, rfl⟩ | inRest
        · exact .inl (List.mem_cons_self ..)
        · rcases ih inRest with old | new
          · exact .inl (List.mem_cons_of_mem _ old)
          · exact .inr new

private theorem replace_getElem_other {values updated : List Dynamic.Value} {index other : Nat}
    {replacement : Dynamic.Value} (replace : Dynamic.ValuesReplaceAt values index replacement updated)
    (different : other ≠ index) : updated[other]? = values[other]? := by
  induction replace generalizing other with
  | head =>
      cases other with
      | zero => exact (different rfl).elim
      | succ other => rfl
  | tail _ ih =>
      cases other with
      | zero => rfl
      | succ other => exact ih (fun same => different (congrArg (· + 1) same))

private theorem ofNatModulo_injective {left right : Nat} (leftBound : left < Core.wordModulus)
    (rightBound : right < Core.wordModulus) (same : Core.Word.ofNatModulo left = Core.Word.ofNatModulo right) :
    left = right := by
  have values := congrArg Fin.val same
  simp only [Core.Word.ofNatModulo, Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound] at values
  exact values

/-- Writing a position below the length: the Source replaces the element, Core inserts its entry. -/
theorem ArrayContents.write {mapping : LocationMap} {world : Core.StoreTyping} {element : Ty}
    {elements updated : List Dynamic.Value} {payload : Core.Ty} {identity : Core.DataTypeId}
    {default : Core.Value} {entries : Core.OrderedMapping.Entries} {position : Nat}
    {source : Dynamic.Value} {core : Core.Value}
    (contents : ArrayContents model mapping world element elements payload identity default entries)
    (replace : Dynamic.ValuesReplaceAt elements position source updated)
    (sourceRep : model.Represents mapping world element source core payload) :
    ArrayContents model mapping world element updated payload identity default
      (Core.OrderedMapping.insertEntries arrayKeyEqual (.word (Core.Word.ofNatModulo position)) core entries) := by
  have length := replace.length_eq
  have selected := replace.selects_replacement.getElem?_eq
  have positionBound : position < elements.length := length ▸ replace.selects_replacement.lt_length
  refine ⟨contents.projection, contents.registered, length ▸ contents.bounded, contents.default_typed, ?_, ?_, ?_⟩
  · intro key value member
    rcases mem_insertEntries member with old | ⟨rfl, _⟩
    · obtain ⟨other, below, same⟩ := contents.keys key value old
      exact ⟨other, length ▸ below, same⟩
    · exact ⟨position, length ▸ positionBound, rfl⟩
  · intro key value member
    rcases mem_insertEntries member with old | ⟨_, rfl⟩
    · exact contents.entries_typed key value old
    · exact model.runtime_hasType sourceRep
  · intro other below
    by_cases same : other = position
    · subst same
      have entry : arrayEntry (Core.OrderedMapping.insertEntries arrayKeyEqual
          (.word (Core.Word.ofNatModulo other)) core entries) default other = core := by
        simp [arrayEntry, lookupEntries_insert_same]
      have sourceEq : updated[other] = source := by
        have := selected
        rw [List.getElem?_eq_getElem below] at this
        exact Option.some.inj this
      rw [entry, sourceEq]
      exact sourceRep
    · have oldBelow : other < elements.length := length ▸ below
      have keysDiffer : (Core.Value.word (Core.Word.ofNatModulo other)) ≠ .word (Core.Word.ofNatModulo position) := by
        intro equal
        injection equal with wordsEqual
        exact same (ofNatModulo_injective (Nat.lt_trans oldBelow contents.bounded)
          (Nat.lt_trans positionBound contents.bounded) wordsEqual)
      have entry : arrayEntry (Core.OrderedMapping.insertEntries arrayKeyEqual
          (.word (Core.Word.ofNatModulo position)) core entries) default other = arrayEntry entries default other := by
        simp only [arrayEntry, lookupEntries_insert_other keysDiffer]
      have elementEq : updated[other] = elements[other] := by
        have := replace_getElem_other replace same
        rw [List.getElem?_eq_getElem below, List.getElem?_eq_getElem oldBelow] at this
        exact Option.some.inj this
      rw [entry, elementEq]
      exact contents.represented other oldBelow

end Solcore.SourceSemantics.CoreLowering.GenericHeap
end

section
/-! Allocating and writing array objects' cells in a whole-cell heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericHeap
open Frontend Frontend.SourceInference TypeSystem GeneralHeap

variable {definitions : Core.DataEnvironment} {model : CellModel definitions}

/-- Append an array object's cell and its Core cell. Source and native locations use their heaps' lengths. -/
theorem CellHeapRepresents.append_array
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store : Core.Store}
    {cell : Dynamic.Cell} {value : Core.Value} {type : Core.Ty}
    (related : CellHeapRepresents model mapping world heap store)
    (represented : model.Array mapping world cell value type) :
    CellHeapRepresents model (mapping ++ [store.length]) (world ++ [type])
      ⟨heap.cells ++ [cell]⟩ (store.allocate value).1 ∧
    (mapping ++ [store.length])[heap.cells.length]? = some store.length ∧
      (world ++ [type])[store.length]? = some type := by
  have extension : Core.WorldExtends world (world ++ [type]) := ⟨_, rfl⟩
  have freshType : (world ++ [type])[store.length]? = some type := by
    rw [← related.runtime_hasTypes.length_eq]; simp
  have freshMap : (mapping ++ [store.length])[heap.cells.length]? = some store.length := by
    rw [← related.length_eq]; simp
  refine ⟨⟨?_, LocationMap.Injective.append related.injective store.length ?_,
    related.runtime_hasTypes.allocate (model.array_runtime_hasType represented), ?_⟩, freshMap, freshType⟩
  · simp [related.length_eq]
  · intro index impossible
    have bound := related.target_lt impossible
    omega
  · intro source target mapped
    rcases cell_append_lookup mapped with old | ⟨sourceEq, targetEq⟩
    · obtain ⟨oldCell, oldValue, sourceRead, coreRead, stands⟩ := related.cells old
      cases sourceRead with
      | intro sourceAt =>
        exact ⟨oldCell, oldValue, .intro sourceAt.append_left,
          (Core.Store.allocate_old_lookup store value (related.target_lt old)).trans coreRead,
          stands.extend ⟨[store.length], rfl⟩ extension⟩
    · subst target
      rw [related.length_eq] at sourceEq
      subst source
      exact ⟨cell, value, .intro (Dynamic.Heap.CellAt.append_last _ _),
        Core.Store.allocate_fresh_lookup store value,
        .array freshType (model.array_extend represented ⟨[store.length], rfl⟩ extension)⟩

/-- An array object's allocation appends its cell, and its Core cell at the store's length. -/
theorem CellHeapRepresents.allocate_array
    {mapping : LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap} {store : Core.Store}
    {element : Ty} {elements : List Dynamic.Value} {location : Dynamic.Location}
    {value : Core.Value} {type : Core.Ty}
    (related : CellHeapRepresents model mapping world heap store)
    (represented : model.Array mapping world
      ⟨.arrayObject element, some (.arrayObject element elements), none⟩ value type)
    (allocated : Dynamic.Heap.Allocates heap (.arrayObject element) (some (.arrayObject element elements))
      location after) :
    CellHeapRepresents model (mapping ++ [store.length]) (world ++ [type]) after (store.allocate value).1 ∧
    (mapping ++ [store.length])[location.index]? = some store.length ∧
      (world ++ [type])[store.length]? = some type := by
  cases allocated
  exact related.append_array represented

/-- Writing an array object's cell replaces it with another array cell at the same mapped location and
Core type. Map injectivity keeps every other cell. -/
theorem CellHeapRepresents.replace_array
    {mapping : LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap} {store : Core.Store}
    {location : Dynamic.Location} {target : Core.Location} {type : Core.Ty}
    {replacement : Dynamic.Cell} {value : Core.Value}
    (related : CellHeapRepresents model mapping world heap store)
    (mapped : mapping[location.index]? = some target) (typed : world[target]? = some type)
    (written : Dynamic.Heap.CellsWrite heap.cells location.index replacement after.cells)
    (newCell : model.Array mapping world replacement value type) :
    ∃ updated, store.write? target value = some updated ∧
      CellHeapRepresents model mapping world after updated := by
  obtain ⟨updated, coreWritten⟩ := related.runtime_hasTypes.write_exists (value := value) typed
  refine ⟨updated, coreWritten, ⟨related.length_eq.trans written.length_eq.symm,
    related.injective, related.runtime_hasTypes.write typed
      (model.array_runtime_hasType newCell) coreWritten, ?_⟩⟩
  intro source other otherMapped
  obtain ⟨cell, stored, sourceRead, coreRead, stands⟩ := related.cells otherMapped
  by_cases same : source = location.index
  · subst source
    have targetEq : other = target := Option.some.inj (otherMapped.symm.trans mapped)
    subst other
    exact ⟨replacement, value, .intro written.reads_replacement,
      Core.Store.write?_reads_written coreWritten, .array typed newCell⟩
  · have different : other ≠ target := by
      intro equal
      exact same (related.injective (equal ▸ otherMapped) mapped)
    cases sourceRead with
    | intro sourceAt =>
        exact ⟨cell, stored, .intro (written.preserves_other same sourceAt),
          (Core.Store.write?_preserves_other coreWritten different).trans coreRead, stands⟩

end Solcore.SourceSemantics.CoreLowering.GenericHeap
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericCellHeapOperations
/-! Ordinary operations in a heap which may also retain generalized cells.
Only the cell actually read or written needs an ordinary storage receipt.
The other cells, the source heap and the native location map stay intact. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericHeap
open Core Frontend SourceInference TypeSystem GeneralHeap

structure OrdinaryCells {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection}
    {definitions : DataEnvironment} (payloads : PayloadModel catalog projects definitions)
    (cells : CellModel definitions) : Prop where
  inject : ∀ {mapping world cell value type},
    CellRepresents payloads mapping world cell value type →
    cells.Represents mapping world cell value type
  project : ∀ {mapping world cell value type},
    cells.Represents mapping world cell value type → cell.generalized = none →
    CellRepresents payloads mapping world cell value type

theorem OrdinaryCells.ordinary {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection}
    {definitions : DataEnvironment} (payloads : PayloadModel catalog projects definitions) :
    OrdinaryCells payloads (.ordinary payloads) := ⟨fun value => value, fun value _ => value⟩

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection} {definitions : DataEnvironment}
  {payloads : PayloadModel catalog projects definitions} {cells : CellModel definitions}

theorem CellHeapRepresents.fresh_unmapped {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} (heaps : CellHeapRepresents cells mapping world heap store) :
    ∀ {source : Nat}, mapping[source]? ≠ some store.length := by
  intro source mapped
  exact Nat.lt_irrefl _ (heaps.target_lt mapped)

theorem CellHeapRepresents.read_ordinary (ordinary : OrdinaryCells payloads cells)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (heaps : CellHeapRepresents cells mapping world heap store)
    (read : Dynamic.Heap.Reads heap location cell) (absent : cell.generalized = none)
    (notArray : ∀ element elements, cell ≠ ⟨.arrayObject element, some (.arrayObject element elements), none⟩) :
    ∃ target value type, ReferenceRepresents mapping world location target type ∧
      store.read? target = some value ∧ CellRepresents payloads mapping world cell value type := by
  obtain ⟨target, value, type, reference, found, related⟩ := heaps.read read notArray
  exact ⟨target, value, type, reference, found, ordinary.project related absent⟩

theorem CellHeapRepresents.write_initialized (ordinary : OrdinaryCells payloads cells)
    {mapping : LocationMap} {world : StoreTyping} {heap after : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {target : Core.Location} {type : Core.Ty}
    {cell : Dynamic.Cell} {source : Dynamic.Value} {native : Core.Value}
    (heaps : CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target type)
    (read : Dynamic.Heap.Reads heap location cell) (absent : cell.generalized = none)
    (represented : payloads.Represents mapping world cell.type source native type)
    (written : Dynamic.Heap.Writes heap location (some source) after) :
    ∃ updated, store.write? target (.inRight .unit native) = some updated ∧
      CellHeapRepresents cells mapping world after updated ∧
      AdministrativePreserved mapping store mapping updated := by
  cases written with
  | @intro previous sourceCells previousRead written =>
      have same := read.functional previousRead
      subst previous
      have replacement : cells.Represents mapping world {cell with value := some source}
          (.inRight .unit native) type := by
        apply ordinary.inject
        cases cell
        simp only at absent represented ⊢
        subst_vars
        exact .initialized represented
      obtain ⟨updated, coreWritten, final⟩ := heaps.replace reference written replacement
      exact ⟨updated, coreWritten, final,
        AdministrativePreserved.write (List.mem_of_getElem? reference.mapped) coreWritten⟩

theorem CellHeapRepresents.bind_ordinary (ordinary : OrdinaryCells payloads cells)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment} {canonical : Core.Environment}
    {heap after : Dynamic.Heap} {store : Store} {id : Resolved.LocalId}
    {sourceType : TypeSystem.Ty} {sourceValue : Option Dynamic.Value} {location : Dynamic.Location}
    {value : Core.Value} {type : Core.Ty}
    (environments : EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : CellHeapRepresents cells mapping world heap store)
    (represented : CellRepresents payloads mapping world ⟨sourceType, sourceValue, none⟩ value type)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    EnvRepresents catalog (mapping ++ [store.length]) (world ++ [OptionalCell.cellType type])
      administrative ((id, type) :: scope) ((id, location) :: environment)
      (.cellRef (OptionalCell.cellType type) store.length :: canonical) definitions ∧
      CellHeapRepresents cells (mapping ++ [store.length]) (world ++ [OptionalCell.cellType type])
        after (store.allocate value).1 := by
  obtain ⟨next, reference⟩ := heaps.allocate_ordinary (ordinary.inject represented) allocated
  exact ⟨.cons reference (environments.extend ⟨_, rfl⟩ ⟨_, rfl⟩), next⟩

end Solcore.SourceSemantics.CoreLowering.GenericHeap
end
