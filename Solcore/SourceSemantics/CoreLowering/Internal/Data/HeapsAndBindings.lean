import Solcore.SourceSemantics.CoreLowering.Internal.Data.Patterns
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.Heaps
import Solcore.Frontend.SourceCoreDefaultValue
import Solcore.SourceSemantics.Dynamic.Default
import Solcore.Core.Correspondence

/-!
# Data: heaps and bindings

The data heap and environment, defaults, mapping comparison and pattern bindings.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataHeap
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataEnvironment
/-! Lexical environments for catalog-indexed cells, with explicit internal Core
slots. An internal slot is a typed Core cell with no source lexical binding: a
match scrutinee, whose cell the source heap also holds, or a closure's copy of
one, which the source heap does not hold. Internal slots therefore extend the
compiler scope and Core environment while preserving the source environment.
Freshness prevents an internal name from hiding a source binding. This
relation does not make internal IDs readable source locals merely because the
low-level compiler can look them up. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataHeap
open Frontend Frontend.SourceInference GeneralHeap

inductive EnvRepresentsIn (catalog : SourceCoreDataCatalog.Catalog) (definitions : Core.DataEnvironment) (mapping : LocationMap)
    (world : Core.StoreTyping) (administrativeContext : Core.Context := []) :
    SourceCoreLocalCell.Scope → Dynamic.Environment → Core.Environment → Prop where
  | nil {administrative : Core.Environment}
      (typed : Core.RuntimeEnvironmentHasTypes world administrative administrativeContext definitions) :
      EnvRepresentsIn catalog definitions mapping world administrativeContext [] [] administrative
  | cons {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
      {coreEnvironment : Core.Environment} {id : Resolved.LocalId}
      {source : Dynamic.Location} {target : Core.Location} {payload : Core.Ty}
      (reference : ReferenceRepresents mapping world source target payload)
      (tail : EnvRepresentsIn catalog definitions mapping world administrativeContext scope environment coreEnvironment) :
      EnvRepresentsIn catalog definitions mapping world administrativeContext ((id, payload) :: scope)
        ((id, source) :: environment)
        (.cellRef (Core.OptionalCell.cellType payload) target :: coreEnvironment)
  | internal {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
      {coreEnvironment : Core.Environment} {id : Resolved.LocalId}
      {target : Core.Location} {payload : Core.Ty}
      (typed : world[target]? = some (Core.OptionalCell.cellType payload))
      (absent : ∀ location, ¬ Dynamic.Environment.LooksUp environment id location)
      (tail : EnvRepresentsIn catalog definitions mapping world administrativeContext scope environment coreEnvironment) :
      EnvRepresentsIn catalog definitions mapping world administrativeContext ((id, payload) :: scope) environment
        (.cellRef (Core.OptionalCell.cellType payload) target :: coreEnvironment)

/-- Source metadata stays with its catalog, while administrative values use
an independently named full Core definition environment. Legacy callers default
to the catalog's definitions. -/
abbrev EnvRepresents (catalog : SourceCoreDataCatalog.Catalog) (mapping : LocationMap)
    (world : Core.StoreTyping) (administrativeContext : Core.Context := [])
    (scope : SourceCoreLocalCell.Scope) (environment : Dynamic.Environment) (coreEnvironment : Core.Environment)
    (definitions : Core.DataEnvironment := catalog.definitions) : Prop :=
  EnvRepresentsIn catalog definitions mapping world administrativeContext scope environment coreEnvironment

namespace EnvRepresents
export EnvRepresentsIn (nil cons internal)
end EnvRepresents

variable {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures} {definitions : Core.DataEnvironment}

/-- World and location-map extension leave every captured source location and
Core reference unchanged. -/
theorem EnvRepresents.extend {mapping futureMapping : LocationMap} {world futureWorld : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    (related : EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment definitions)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : Core.WorldExtends world futureWorld) :
    EnvRepresents catalog futureMapping futureWorld administrativeContext scope environment coreEnvironment definitions := by
  induction related with
  | nil typed => exact .nil (typed.weaken worlds)
  | cons reference _ ih => exact .cons (reference.extend maps worlds) ih
  | internal typed absent _ ih => exact .internal (Core.WorldExtends.lookup worlds typed) absent ih

theorem EnvRepresents.runtime_hasTypes {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    (related : EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment definitions) :
    Core.RuntimeEnvironmentHasTypes world coreEnvironment
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) definitions := by
  induction related with
  | nil typed => exact typed
  | cons reference _ ih => exact .cons (.cellRef reference.typed) ih
  | internal typed _ _ ih => exact .cons (.cellRef typed) ih

/-- Every actual source lexical binding is present at the compiler's first
matching slot, even with internal slots interspersed between lexical scopes. -/
theorem EnvRepresents.lookup_source {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {id : Resolved.LocalId} {location : Dynamic.Location}
    (related : EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment definitions)
    (sourceLookup : Dynamic.Environment.LooksUp environment id location) :
    ∃ index payload target,
      SourceCoreLocalCell.lookup? scope id = some (index, payload) ∧
      coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType payload) target) ∧
      ReferenceRepresents mapping world location target payload := by
  induction related with
  | nil => cases sourceLookup
  | @cons scope environment coreEnvironment other source target payload reference tail ih =>
    cases sourceLookup with
    | head => exact ⟨0, payload, target, by simp [SourceCoreLocalCell.lookup?], rfl, reference⟩
    | tail different sourceLookup =>
      obtain ⟨index, type, found, slot, coreLookup, reference⟩ := ih sourceLookup
      exact ⟨index + 1, type, found, by simp [SourceCoreLocalCell.lookup?, different, slot], coreLookup, reference⟩
  | @internal scope environment coreEnvironment other target payload typed absent tail ih =>
    have different : other ≠ id := by intro same; subst other; exact absent location sourceLookup
    obtain ⟨index, type, found, slot, coreLookup, reference⟩ := ih sourceLookup
    exact ⟨index + 1, type, found, by simp [SourceCoreLocalCell.lookup?, different, slot], coreLookup, reference⟩

/-- A compiler lookup can be used as a source read only with lexical visibility.
This is the deliberate boundary excluding fabricated references to hidden IDs. -/
theorem EnvRepresents.lookup_visible {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {id : Resolved.LocalId} {location : Dynamic.Location} {index : Nat} {payload : Core.Ty}
    (related : EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment definitions)
    (sourceLookup : Dynamic.Environment.LooksUp environment id location)
    (slot : SourceCoreLocalCell.lookup? scope id = some (index, payload)) :
    ∃ target, coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType payload) target) ∧
      ReferenceRepresents mapping world location target payload := by
  obtain ⟨otherIndex, otherPayload, target, otherSlot, coreLookup, reference⟩ := related.lookup_source sourceLookup
  have same := Option.some.inj (otherSlot.symm.trans slot)
  cases same
  exact ⟨target, coreLookup, reference⟩

private theorem lookup_implies_any {scope : SourceCoreLocalCell.Scope} {id : Resolved.LocalId}
    {index : Nat} {payload : Core.Ty} (slot : SourceCoreLocalCell.lookup? scope id = some (index, payload)) :
    scope.any (fun entry => decide (entry.1 = id)) = true := by
  induction scope generalizing index payload with
  | nil => simp [SourceCoreLocalCell.lookup?] at slot
  | cons entry rest ih =>
    obtain ⟨other, type⟩ := entry
    by_cases same : other = id
    · simp [same]
    · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at slot
      cases found : SourceCoreLocalCell.lookup? rest id with
      | none => simp [found] at slot
      | some selected =>
        obtain ⟨selectedIndex, selectedType⟩ := selected
        simpa using Or.inr (ih found)

/-- The compiler's hidden-ID freshness check suffices to prove absence from
the independently represented source environment. -/
theorem EnvRepresents.fresh_absent {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment} {id : Resolved.LocalId}
    (related : EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment definitions)
    (fresh : scope.any (fun entry => decide (entry.1 = id)) = false) :
    ∀ location, ¬ Dynamic.Environment.LooksUp environment id location := by
  intro location lookup
  obtain ⟨_, _, _, slot, _, _⟩ := related.lookup_source lookup
  have present := lookup_implies_any slot
  rw [fresh] at present
  contradiction

/-- Ordinary source binding allocates at independent source and Core lengths. -/
theorem EnvRepresents.bind {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {heap after : Dynamic.Heap} {store : Core.Store} {id : Resolved.LocalId}
    {sourceType : TypeSystem.Ty} {sourceValue : Option Dynamic.Value} {location : Dynamic.Location}
    {value : Core.Value} {payload : Core.Ty}
    (environments : EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents catalog signatures mapping world heap store)
    (cell : CellRepresents catalog signatures ⟨sourceType, sourceValue, none⟩ value payload)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    EnvRepresents catalog (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      administrativeContext ((id, payload) :: scope) ((id, location) :: environment)
      (.cellRef (Core.OptionalCell.cellType payload) store.length :: coreEnvironment) ∧
    HeapRepresents catalog signatures (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      after (store.allocate value).1 := by
  obtain ⟨heapRelated, reference⟩ := heaps.allocate cell allocated
  exact ⟨.cons reference (environments.extend ⟨_, rfl⟩ ⟨_, rfl⟩), heapRelated⟩

/-- Match's hidden cell is allocated on both sides, but bound only in Core. -/
theorem EnvRepresents.bind_internal {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {heap after : Dynamic.Heap} {store : Core.Store} {id : Resolved.LocalId}
    {sourceType : TypeSystem.Ty} {sourceValue : Option Dynamic.Value} {location : Dynamic.Location}
    {value : Core.Value} {payload : Core.Ty}
    (environments : EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents catalog signatures mapping world heap store)
    (fresh : scope.any (fun entry => decide (entry.1 = id)) = false)
    (cell : CellRepresents catalog signatures ⟨sourceType, sourceValue, none⟩ value payload)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    EnvRepresents catalog (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      administrativeContext ((id, payload) :: scope) environment
      (.cellRef (Core.OptionalCell.cellType payload) store.length :: coreEnvironment) ∧
    HeapRepresents catalog signatures (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      after (store.allocate value).1 := by
  obtain ⟨heapRelated, reference⟩ := heaps.allocate cell allocated
  exact ⟨.internal reference.typed (environments.fresh_absent fresh)
    (environments.extend ⟨_, rfl⟩ ⟨_, rfl⟩), heapRelated⟩

namespace EnvRepresentsIn
abbrev extend := @EnvRepresents.extend
abbrev runtime_hasTypes := @EnvRepresents.runtime_hasTypes
abbrev lookup_source := @EnvRepresents.lookup_source
abbrev lookup_visible := @EnvRepresents.lookup_visible
abbrev fresh_absent := @EnvRepresents.fresh_absent
end EnvRepresentsIn

end Solcore.SourceSemantics.CoreLowering.DataHeap
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataMappingComparison
/-! Instantiate the ordinary mapping library with the actual prepared source
comparator. Mathematical predicate witnesses occur only inside proofs. Executed
comparisons use the generated Core closure, whose finite evaluations are
derived from represented keys and installed helper cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMappingComparison
open Core Frontend SourceCoreDataEquality DataEquality DataEqualityValues DataEqualityCertificates

abbrev KeyRep {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (signatures : ProgramSignatures) (identities : Dynamic.Value → Word → Prop) :=
  Observation checked.catalog signatures identities prepared.type

def comparator {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (environment : Environment) (store : Store) : Value :=
  .closure (.product prepared.type prepared.type) .bool
    (prepared.body.rename (DataEqualityInstalled.offset prepared.bodies.length).lift)
    (DataEqualityInstalled.captured prepared.bodies.length
      (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length environment))

def comparisonStore {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (environment : Environment) (store : Store) : Store :=
  store ++ DataEqualityInstalled.cells
    (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length environment) prepared.bodies

/-- Two equality observations of the same Core values agree on source
equivalence. This follows from the actual comparator's deterministic finite
execution, without assuming injectivity of unobserved mapping contents/code. -/
theorem equivalent_coherent {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    {a b c d : Dynamic.Value} {left right : Value}
    (aRep : KeyRep prepared signatures identities a left) (bRep : KeyRep prepared signatures identities b right)
    (cRep : KeyRep prepared signatures identities c left) (dRep : KeyRep prepared signatures identities d right) :
    Dynamic.ValueEquivalent a b ↔ Dynamic.ValueEquivalent c d := by
  have installed := DataEqualityInstalled.prepared_installed prepared [] []
  obtain ⟨first, firstTree⟩ := prepared_tree prepared aRep bRep [] [] _ installed
  obtain ⟨second, secondTree⟩ := prepared_tree prepared cRep dRep [] [] _ installed
  have same := Value.bool.inj (evaluation_deterministic firstTree.evaluates secondTree.evaluates).1
  exact (firstTree.meaning faithful).symm.trans (same ▸ secondTree.meaning faithful)

theorem exists_predicate_correct {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (signatures : ProgramSignatures) {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) :
    ∃ equal : Core.OrderedMapping.Predicate,
      OrderedMapping.KeyEqualityCorrect (KeyRep prepared signatures identities) equal := by
  classical
  let equal : Core.OrderedMapping.Predicate := fun left right => decide
    (∃ a b, KeyRep prepared signatures identities a left ∧ KeyRep prepared signatures identities b right ∧
      Dynamic.ValueEquivalent a b)
  refine ⟨equal, ?_⟩
  constructor
  intro sourceKey sourceStored key stored keyRep storedRep
  simp only [equal, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, aRep, bRep, equivalent⟩
    exact (equivalent_coherent prepared faithful aRep bRep keyRep storedRep).mp equivalent
  · intro equivalent
    exact ⟨_, _, keyRep, storedRep, equivalent⟩

theorem entries_key {keyRel valueRel : OrderedMapping.Relation}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (related : OrderedMapping.EntriesRel keyRel valueRel sources entries)
    {key value : Value} (member : (key, value) ∈ entries) :
    ∃ sourceKey sourceValue, keyRel sourceKey key ∧ valueRel sourceValue value := by
  induction related with
  | nil => simp at member
  | cons keyRep valueRep tail ih =>
    rcases List.mem_cons.mp member with same | remaining
    · cases same
      exact ⟨_, _, keyRep, valueRep⟩
    · exact ih remaining

theorem comparisons {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (equal : Core.OrderedMapping.Predicate)
    (correct : OrderedMapping.KeyEqualityCorrect (KeyRep prepared signatures identities) equal)
    {valueRel : OrderedMapping.Relation}
    {sourceKey : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep prepared signatures identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep prepared signatures identities) valueRel sources entries)
    (environment : Environment) (initialStore store : Store)
    (installed : DataEqualityInstalled.Installed checked.catalog prepared.bodies initialStore.length environment store) :
    Core.OrderedMapping.Comparisons layout (comparator prepared environment initialStore)
      equal key entries store := by
  intro stored value member
  obtain ⟨sourceStored, _, storedRep, _⟩ := entries_key related member
  obtain ⟨result, meaning, compared⟩ := prepared_compares prepared layout keyType faithful keyRep storedRep
    environment initialStore store installed
  have equivalent := correct.equivalent keyRep storedRep
  have same : result = equal key stored := by
    cases result <;> cases generated : equal key stored <;> simp_all
  subst result
  exact compared

def lookupStore {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (environment : Environment) (store : Store)
    (entries : Core.OrderedMapping.Entries) (key : Value) : Store :=
  Core.OrderedMapping.installedStore (comparisonStore prepared environment store)
    layout.lookupParameter layout.lookupResult (Core.OrderedMapping.lookupBody layout)
    (.pair (Core.OrderedMapping.encode layout entries) (.pair key (comparator prepared environment store))) environment

def insertStore {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (environment : Environment) (store : Store)
    (entries : Core.OrderedMapping.Entries) (key value : Value) : Store :=
  Core.OrderedMapping.installedStore (comparisonStore prepared environment store)
    layout.insertParameter layout.type (Core.OrderedMapping.insertBody layout)
    (.pair (Core.OrderedMapping.encode layout entries) (.pair (.pair key value) (comparator prepared environment store))) environment

theorem lookup_evaluates {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (equal : Core.OrderedMapping.Predicate)
    (correct : OrderedMapping.KeyEqualityCorrect (KeyRep prepared signatures identities) equal)
    {valueRel : OrderedMapping.Relation}
    {sourceKey : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep prepared signatures identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep prepared signatures identities) valueRel sources entries)
    (environment : Environment) (store : Store) (mapping keyExpression : Expr)
    (mappingSelected : Selects environment mapping (Core.OrderedMapping.encode layout entries))
    (keySelected : Selects environment keyExpression key) :
    Evaluates environment store (Core.OrderedMapping.lookup layout prepared.expression mapping keyExpression)
      (.inRight .word (Core.OrderedMapping.optionValue layout.valueType
        (Core.OrderedMapping.lookupEntries equal key entries)))
      (lookupStore prepared layout environment store entries key) := by
  apply Core.OrderedMapping.lookup_evaluates entries key (comparator prepared environment store)
    equal (mappingSelected.evaluates store) (keySelected.evaluates store)
    (DataEqualityInstalled.prepared_evaluates_exact prepared environment store)
  apply comparisons prepared layout keyType faithful equal correct keyRep related
  exact installed_append (DataEqualityInstalled.prepared_installed prepared environment store) _

theorem insert_evaluates {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (equal : Core.OrderedMapping.Predicate)
    (correct : OrderedMapping.KeyEqualityCorrect (KeyRep prepared signatures identities) equal)
    {valueRel : OrderedMapping.Relation}
    {sourceKey : Dynamic.Value} {key value : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep prepared signatures identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep prepared signatures identities) valueRel sources entries)
    (environment : Environment) (store : Store) (mapping keyExpression valueExpression : Expr)
    (mappingSelected : Selects environment mapping (Core.OrderedMapping.encode layout entries))
    (keySelected : Selects environment keyExpression key) (valueSelected : Selects environment valueExpression value) :
    Evaluates environment store (Core.OrderedMapping.insert layout prepared.expression mapping keyExpression valueExpression)
      (.inRight .word (Core.OrderedMapping.encode layout
        (Core.OrderedMapping.insertEntries equal key value entries)))
      (insertStore prepared layout environment store entries key value) := by
  apply Core.OrderedMapping.insert_evaluates entries key value (comparator prepared environment store)
    equal (mappingSelected.evaluates store) (keySelected.evaluates store)
    (valueSelected.evaluates store) (DataEqualityInstalled.prepared_evaluates_exact prepared environment store)
  apply comparisons prepared layout keyType faithful equal correct keyRep related
  exact installed_append (DataEqualityInstalled.prepared_installed prepared environment store) _

theorem lookup_found {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceValue : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep prepared signatures identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep prepared signatures identities) valueRel sources entries)
    (found : Dynamic.MappingLookup sourceKey sources sourceValue)
    (environment : Environment) (store : Store) (mapping keyExpression : Expr)
    (mappingSelected : Selects environment mapping (Core.OrderedMapping.encode layout entries))
    (keySelected : Selects environment keyExpression key) :
    ∃ value, valueRel sourceValue value ∧
      Evaluates environment store (Core.OrderedMapping.lookup layout prepared.expression mapping keyExpression)
        (.inRight .word (.inRight .unit value)) (lookupStore prepared layout environment store entries key) := by
  obtain ⟨equal, correct⟩ := exists_predicate_correct prepared signatures faithful
  obtain ⟨value, selected, represented⟩ := OrderedMapping.lookup_related correct keyRep related found
  have evaluated := lookup_evaluates prepared layout keyType faithful equal correct keyRep related environment store mapping keyExpression mappingSelected keySelected
  rw [selected] at evaluated
  exact ⟨value, represented, evaluated⟩

theorem lookup_absent {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep prepared signatures identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep prepared signatures identities) valueRel sources entries)
    (absent : Dynamic.MappingAbsent sourceKey sources)
    (environment : Environment) (store : Store) (mapping keyExpression : Expr)
    (mappingSelected : Selects environment mapping (Core.OrderedMapping.encode layout entries))
    (keySelected : Selects environment keyExpression key) :
    Evaluates environment store (Core.OrderedMapping.lookup layout prepared.expression mapping keyExpression)
      (.inRight .word (.inLeft layout.valueType .unit)) (lookupStore prepared layout environment store entries key) := by
  obtain ⟨equal, correct⟩ := exists_predicate_correct prepared signatures faithful
  have evaluated := lookup_evaluates prepared layout keyType faithful equal correct keyRep related environment store mapping keyExpression mappingSelected keySelected
  rw [OrderedMapping.absent_related correct keyRep related absent] at evaluated
  exact evaluated

theorem insert_preserves {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceValue : Dynamic.Value} {key value : Value}
    {sources updated : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep prepared signatures identities sourceKey key) (valueRep : valueRel sourceValue value)
    (related : OrderedMapping.EntriesRel (KeyRep prepared signatures identities) valueRel sources entries)
    (inserted : Dynamic.MappingInsert sourceKey sourceValue sources updated)
    (environment : Environment) (store : Store) (mapping keyExpression valueExpression : Expr)
    (mappingSelected : Selects environment mapping (Core.OrderedMapping.encode layout entries))
    (keySelected : Selects environment keyExpression key) (valueSelected : Selects environment valueExpression value) :
    ∃ output, OrderedMapping.ValueRel layout (KeyRep prepared signatures identities) valueRel updated output ∧
      Evaluates environment store (Core.OrderedMapping.insert layout prepared.expression mapping keyExpression valueExpression)
        (.inRight .word output) (insertStore prepared layout environment store entries key value) := by
  obtain ⟨equal, correct⟩ := exists_predicate_correct prepared signatures faithful
  exact ⟨_, ⟨_, OrderedMapping.insert_related correct keyRep valueRep related inserted, rfl⟩,
    insert_evaluates prepared layout keyType faithful equal correct keyRep related environment store mapping keyExpression valueExpression
      mappingSelected keySelected valueSelected⟩

/-- One operation appends the comparator's complete helper table, then one
mapping helper. Every preexisting cell keeps its exact value. -/
theorem helper_store_extension {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (environment : Environment) (store : Store) (parameter result : Ty) (body : Expr) (input : Value) :
    ∃ administrative,
      Core.OrderedMapping.installedStore (comparisonStore prepared environment store) parameter result body input environment =
        store ++ administrative ∧ administrative.length = checked.catalog.entries.length + 1 := by
  obtain ⟨administrative, same, count⟩ := DataEqualityInitializationStore.prepared_store_extension prepared
    (DataEqualityInstalled.prepared_evaluates_exact prepared environment store)
  refine ⟨administrative ++ [.inRight .unit (Core.WordMapping.closure parameter result body
    (comparisonStore prepared environment store).length (input :: environment))], ?_, by simp [count]⟩
  change comparisonStore prepared environment store ++ _ = store ++ _
  rw [show comparisonStore prepared environment store = store ++ administrative from same]
  simp only [List.append_assoc]

end Solcore.SourceSemantics.CoreLowering.DataMappingComparison
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataDefaults
set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.DataDefaults

open Core Frontend
open SourceCoreDefaultValue

/-- The proxy/mapping identity is the exact catalog lookup. No arbitrary
runtime proxy payload is normalized into this relation. -/
inductive Tree (catalog : SourceCoreDataCatalog.Catalog) :
    TypeSystem.Ty → Dynamic.Value → Value → Expr → Prop where
  | unit : Tree catalog .unit .unit .unit .unit
  | bool : Tree catalog .bool (.bool false) (.bool false) (.bool false)
  | word : Tree catalog .word (.word Word.zero) (.word Word.zero) (.word Word.zero)
  | integer : Tree catalog .integer (.integer 0) (.integer 0) (.integer 0)
  | product {leftTy rightTy : TypeSystem.Ty} {left right : Dynamic.Value}
      {leftValue rightValue : Value} {leftExpr rightExpr : Expr}
      (leftTree : Tree catalog leftTy left leftValue leftExpr)
      (rightTree : Tree catalog rightTy right rightValue rightExpr) :
      Tree catalog (.product leftTy rightTy) (.product left right)
        (.pair leftValue rightValue) (.pair leftExpr rightExpr)
  | proxy (inner : TypeSystem.Ty) (id : DataTypeId)
      (identity : catalog.identity? (.proxy inner) = some id) :
      Tree catalog (.proxy inner) (.proxy inner) (.constructed ⟨id, 0⟩ .unit)
        (.construct ⟨id, 0⟩ .unit)
  | mapping (key value : TypeSystem.Ty) (id : DataTypeId)
      (identity : catalog.identity? (.mapping key value) = some id) :
      Tree catalog (.mapping key value) (.mapping key value [])
        (.constructed ⟨id, 0⟩ .unit) (.construct ⟨id, 0⟩ .unit)
  | comptime {inner : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {expression : Expr}
      (innerTree : Tree catalog inner source value expression) :
      Tree catalog (.comptime inner) source value expression

theorem Tree.meaning {catalog : Catalog} {type : TypeSystem.Ty}
    {source : Dynamic.Value} {value : Value} {expression : Expr}
    (tree : Tree catalog type source value expression) : Dynamic.DefaultValue type source := by
  induction tree with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | product _ _ left right => exact .product left right
  | proxy inner _ _ => exact .proxy inner
  | mapping key value _ _ => exact .mapping key value
  | comptime _ inner => exact .comptime inner

theorem Tree.evaluates {catalog : Catalog} {type : TypeSystem.Ty}
    {source : Dynamic.Value} {value : Value} {expression : Expr}
    (tree : Tree catalog type source value expression) (environment : Environment) (store : Store) :
    Evaluates environment store expression value store := by
  induction tree with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | product _ _ left right => exact .pair left right
  | proxy | mapping => exact .construct .unit
  | comptime _ inner => exact inner

/-- Every accepted present default has an independent source meaning. -/
theorem tree_of_defaultExpression (fuel : Nat) (catalog : Catalog) (type : TypeSystem.Ty)
    (expression : Expr) (accepted : defaultExpression fuel catalog type = .ok (some expression)) :
    ∃ source value, Tree catalog type source value expression := by
  induction fuel generalizing type expression with
  | zero => simp [defaultExpression] at accepted
  | succ fuel ih =>
    cases type with
    | «variable» | parameter | application | function | error => simp [defaultExpression] at accepted
    | constructor constructor =>
      cases constructor with
      | declaration => simp [defaultExpression] at accepted
      | builtin builtin =>
        cases builtin <;> simp [defaultExpression, pure, Except.pure] at accepted <;> subst expression
        · exact ⟨_, _, .unit⟩
        · exact ⟨_, _, .bool⟩
        · exact ⟨_, _, .word⟩
        · exact ⟨_, _, .integer⟩
    | product left right =>
      cases leftResult : defaultExpression fuel catalog left with
      | error => simp [defaultExpression, leftResult, bind, Except.bind] at accepted
      | ok leftExpr =>
        cases rightResult : defaultExpression fuel catalog right with
        | error => simp [defaultExpression, leftResult, rightResult, bind, Except.bind] at accepted
        | ok rightExpr =>
          cases leftExpr <;> cases rightExpr <;>
            simp [defaultExpression, leftResult, rightResult, bind, Except.bind, pure, Except.pure] at accepted
          rename_i leftExpr rightExpr
          subst expression
          obtain ⟨left, leftValue, leftTree⟩ := ih left leftExpr leftResult
          obtain ⟨right, rightValue, rightTree⟩ := ih right rightExpr rightResult
          exact ⟨_, _, .product leftTree rightTree⟩
    | proxy inner =>
      cases identity : catalog.identity? (.proxy inner) with
      | none => simp [defaultExpression, identity] at accepted
      | some id =>
        simp [defaultExpression, identity, pure, Except.pure] at accepted
        subst expression
        exact ⟨_, _, .proxy inner id identity⟩
    | mapping key value =>
      cases identity : catalog.identity? (.mapping key value) with
      | none => simp [defaultExpression, identity] at accepted
      | some id =>
        simp [defaultExpression, identity, pure, Except.pure] at accepted
        subst expression
        exact ⟨_, _, .mapping key value id identity⟩
    | comptime inner =>
      obtain ⟨source, value, tree⟩ := ih inner expression accepted
      exact ⟨source, value, .comptime tree⟩

/-- A successful absent answer never discards a source default. Fuel exhaustion
is an error, not an absent answer. -/
theorem absent_has_no_default (fuel : Nat) (catalog : Catalog) (type : TypeSystem.Ty)
    (accepted : defaultExpression fuel catalog type = .ok none) :
    ∀ source, ¬ Dynamic.DefaultValue type source := by
  induction fuel generalizing type with
  | zero => simp [defaultExpression] at accepted
  | succ fuel ih =>
    intro source meaning
    cases meaning with
    | unit => simp [TypeSystem.Ty.unit, defaultExpression] at accepted
    | bool => simp [TypeSystem.Ty.bool, defaultExpression] at accepted
    | word => simp [TypeSystem.Ty.word, defaultExpression] at accepted
    | integer => simp [TypeSystem.Ty.integer, defaultExpression] at accepted
    | proxy inner =>
      cases identity : catalog.identity? (.proxy inner) <;>
        simp [defaultExpression, identity, pure, Except.pure] at accepted
    | mapping key value =>
      cases identity : catalog.identity? (.mapping key value) <;>
        simp [defaultExpression, identity, pure, Except.pure] at accepted
    | comptime inner => exact ih _ accepted _ inner
    | @product leftTy rightTy _ _ leftDefault rightDefault =>
      cases leftResult : defaultExpression fuel catalog leftTy with
      | error => simp [defaultExpression, leftResult, bind, Except.bind] at accepted
      | ok left =>
        cases rightResult : defaultExpression fuel catalog rightTy with
        | error => simp [defaultExpression, leftResult, rightResult, bind, Except.bind] at accepted
        | ok right =>
          cases left with
          | none => exact ih _ leftResult _ leftDefault
          | some left =>
            cases right with
            | none => exact ih _ rightResult _ rightDefault
            | some right => simp [defaultExpression, leftResult, rightResult, bind, Except.bind, pure, Except.pure] at accepted

/-- Accepted code, independent default meaning, finite execution, and unchanged
store follow together. No executable source evaluator is a premise. -/
theorem defaultExpression_run_preserves (fuel : Nat) (catalog : Catalog) (type : TypeSystem.Ty)
    (expression : Expr) (accepted : defaultExpression fuel catalog type = .ok (some expression))
    (environment : Environment) (store : Store) :
    ∃ source value required, Tree catalog type source value expression ∧
      Dynamic.DefaultValue type source ∧ ∀ budget, required ≤ budget →
        runStateful budget (State.initial expression environment store) = .done value store := by
  obtain ⟨source, value, tree⟩ := tree_of_defaultExpression fuel catalog type expression accepted
  obtain ⟨required, complete⟩ := evaluation_runStateful_complete_with_sufficient_fuel (tree.evaluates environment store)
  exact ⟨source, value, required, tree, tree.meaning, complete⟩

inductive ResultRepresents (catalog : Catalog) (type : TypeSystem.Ty) (coreType : Core.Ty) : Value → Prop where
  | absent (missing : ∀ source, ¬ Dynamic.DefaultValue type source) :
      ResultRepresents catalog type coreType (.inLeft coreType .unit)
  | present {source : Dynamic.Value} {value : Value} {expression : Expr}
      (tree : Tree catalog type source value expression) :
      ResultRepresents catalog type coreType (.inRight .unit value)

/-- Prepared code retains its generator equation, so this public theorem needs
no extra certificate premise and covers both present and absent defaults. -/
theorem prepared_preserves {checked : SourceCoreDataCatalog.Checked}
    (prepared : Prepared checked) (environment : Environment) (store : Store) :
    ∃ value, ResultRepresents checked.catalog prepared.sourceType prepared.type value ∧
      Evaluates environment store prepared.expression value store := by
  cases generatedDefault : prepared.default with
  | none =>
    have generated := prepared.generated
    rw [generatedDefault] at generated
    refine ⟨_, .absent (absent_has_no_default _ _ _ generated), ?_⟩
    rw [prepared.expression_eq, generatedDefault]
    exact .inLeft .unit
  | some expression =>
    have generated := prepared.generated
    rw [generatedDefault] at generated
    obtain ⟨source, value, tree⟩ := tree_of_defaultExpression _ _ _ _ generated
    refine ⟨_, .present tree, ?_⟩
    rw [prepared.expression_eq, generatedDefault]
    exact .inRight (tree.evaluates environment store)

theorem prepared_run_preserves {checked : SourceCoreDataCatalog.Checked}
    (prepared : Prepared checked) (environment : Environment) (store : Store) :
    ∃ value required, ResultRepresents checked.catalog prepared.sourceType prepared.type value ∧
      ∀ budget, required ≤ budget →
        runStateful budget (State.initial prepared.expression environment store) = .done value store := by
  obtain ⟨value, represented, evaluation⟩ := prepared_preserves prepared environment store
  obtain ⟨required, complete⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluation
  exact ⟨value, required, represented, complete⟩

end Solcore.SourceSemantics.CoreLowering.DataDefaults
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPatternBindings
/-! Authenticated binder payloads from a static pattern certificate. The source
binder's declared type is retained separately from its Core projection. These
facts permit ordinary heap allocation after a successful match without treating
an untyped value relation or a matching Core tag as source type evidence. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternBindings
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataPatternCertificates DataPatternValues DataPatternLeaves
open DataPatternTypedValues DataPatternSuccess DataPatternExecution

inductive BindingsRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures) :
    List (TypedBinder × Ty) → List (TypedBinder × Dynamic.Value) → List Value → Prop where
  | nil : BindingsRep catalog signatures [] [] []
  | cons {binder : TypedBinder} {type : Ty} {source : Dynamic.Value} {value : Value}
      {binders : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
      (projection : catalog.project binder.scheme.body = .ok type)
      (head : TypedValueRep catalog signatures binder.scheme.body source value)
      (tail : BindingsRep catalog signatures binders sources values) :
      BindingsRep catalog signatures ((binder, type) :: binders) ((binder, source) :: sources) (value :: values)

theorem BindingsRep.erase {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {binders : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep catalog signatures binders sources values) :
    DataPatternLeaves.BindingsRep catalog binders sources values := by
  induction represented with
  | nil => exact .nil
  | cons _ head _ ih => exact .cons head.erase ih

theorem BindingsRep.append {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {a c : List (TypedBinder × Ty)} {b d : List (TypedBinder × Dynamic.Value)} {v w : List Value}
    (left : BindingsRep catalog signatures a b v) (right : BindingsRep catalog signatures c d w) :
    BindingsRep catalog signatures (a ++ c) (b ++ d) (v ++ w) := by
  induction left with
  | nil => exact right
  | cons projection head _ ih => exact .cons projection head ih

/-- The checked projection retains the same raw catalog type. -/
theorem projected_raw {compilation : Compilation} {source : TypedSource} {type : TypeSystem.Ty} {coreType : Ty}
    (accepted : projected compilation source type = .ok coreType) :
    compilation.checked.catalog.project type = .ok coreType := by
  unfold projected SourceCoreGeneralTypes.projectType at accepted
  cases checked : compilation.checked.project type with
  | error error => simp [checked, Except.mapError, Except.map] at accepted
  | ok projection =>
    simp only [checked, Except.map, Except.mapError, Except.ok.injEq] at accepted
    subst coreType
    unfold SourceCoreDataCatalog.Checked.project at checked
    cases raw : compilation.checked.catalog.project type with
    | error error => simp [raw, bind, Except.bind] at checked
    | ok actual =>
      simp only [raw, bind, Except.bind] at checked
      split at checked
      · cases checked; rfl
      · cases checked

def TreeBindingTypes (compilation : Compilation) (context : SourceSemantics.Context)
    (type : TypeSystem.Ty) (instructions : List MatchPatternInstruction) (pattern : Pattern)
    (rest : List MatchPatternInstruction) : Prop :=
  ∀ source value bindings sourceRest,
    TypedValueRep compilation.checked.catalog compilation.signatures type source value →
    Dynamic.PatternInstructionMatches context source instructions bindings sourceRest →
    ∃ values, sourceRest = rest ∧ BindingsRep compilation.checked.catalog compilation.signatures pattern.bindings bindings values

def ForestBindingTypes (compilation : Compilation) (context : SourceSemantics.Context)
    (types : List TypeSystem.Ty) (instructions : List MatchPatternInstruction) (patterns : List Pattern)
    (rest : List MatchPatternInstruction) : Prop :=
  ∀ sources values bindings sourceRest,
    TypedValuesRep compilation.checked.catalog compilation.signatures types sources values →
    Dynamic.PatternInstructionsMatch context sources instructions bindings sourceRest →
    ∃ boundValues, sourceRest = rest ∧
      BindingsRep compilation.checked.catalog compilation.signatures (patterns.flatMap (·.bindings)) bindings boundValues

/-- Pattern structure, genuine source matching, and the authenticated input
value determine the source types of every allocated binder. No evaluator
premise or heap invariant is needed to derive this certificate. -/
theorem Tree.binding_types {compilation : Compilation} {context : SourceSemantics.Context} {source : TypedSource}
    {site : StatementId} {span : Syntax.SourceSpan} {scope : Scope} {type : TypeSystem.Ty}
    {instructions rest : List MatchPatternInstruction} {pattern : Pattern}
    (tree : Tree compilation source site span scope type instructions pattern rest) :
    TreeBindingTypes compilation context type instructions pattern rest := by
  induction tree using Tree.rec
      (motive_2 := fun types instructions patterns rest _ => ForestBindingTypes compilation context types instructions patterns rest) with
  | wildcard projection =>
    intro source value bindings sourceRest represented matched
    cases matched
    exact ⟨[], rfl, .nil⟩
  | binder projection sourceType valid =>
    intro source value bindings sourceRest represented matched
    cases matched
    refine ⟨[value], rfl, .cons ?_ ?_ .nil⟩
    · rw [sourceType]; exact projected_raw projection
    · rw [sourceType]; exact represented
  | literal projection validated =>
    intro source value bindings sourceRest represented matched
    cases matched
    exact ⟨[], rfl, .nil⟩
  | @tuple expected coreType count types instructions rest children coreTypes projection unpacked childrenTree projectedChildren ih =>
    intro sourceValue value bindings sourceRest represented matched
    cases matched with
    | tuple packed arity matchedChildren =>
      obtain ⟨sources, values, representations, packing, valueEq⟩ := TypedValueRep.unpack unpacked represented
      have sameSources := Dynamic.ValuesPack.injective_of_length_eq packing packed
        ((TypedValuesRep.length representations).1.symm.trans ((unpackTypes_length unpacked).trans arity.symm))
      subst sources
      exact ih _ _ _ _ representations matchedChildren
  | constructor projection result arity resolved sameType childrenTree projectedChildren registered ih =>
    intro sourceValue value bindings sourceRest represented matched
    cases matched with
    | constructor agreement countEq matchedChildren =>
      cases represented with
      | constructed nominal actualResult authenticated payloads =>
        exact ih _ _ _ _ (agreement.payload_types_eq ▸ payloads) matchedChildren
  | nil =>
    intro sources values bindings sourceRest represented matched
    cases represented
    cases matched
    exact ⟨[], rfl, .nil⟩
  | cons headTree tailTree headIH tailIH =>
    intro sources values bindings sourceRest represented matched
    cases represented with
    | cons valueRep valuesRep =>
      cases matched with
      | cons headMatch tailMatch =>
        obtain ⟨headValues, headRestEq, headBindings⟩ := headIH _ _ _ _ valueRep headMatch
        subst headRestEq
        obtain ⟨tailValues, tailRestEq, tailBindings⟩ := tailIH _ _ _ _ valuesRep tailMatch
        exact ⟨headValues ++ tailValues, tailRestEq, headBindings.append tailBindings⟩
/-- The source value and fixed catalog determine its finite Core carrier. -/
theorem value_core_unique {catalog : SourceCoreDataCatalog.Catalog}
    {source : Dynamic.Value} {left right : Value}
    (first : ValueRep catalog source left) (second : ValueRep catalog source right) : left = right := by
  induction first using ValueRep.rec
      (motive_2 := fun sources values _ => ∀ other, ValuesRep catalog sources other → values = other)
      generalizing right with
  | unit => cases second; rfl
  | bool => cases second; rfl
  | word => cases second; rfl
  | integer => cases second; rfl
  | product leftRep rightRep leftIH rightIH =>
    cases second with
    | product otherLeft otherRight => rw [leftIH otherLeft, rightIH otherRight]
  | constructed selected payloads ih =>
    cases second with
    | constructed otherSelected otherPayloads =>
      have same := Option.some.inj (selected.symm.trans otherSelected)
      cases same
      rw [ih _ otherPayloads]
  | nil => rename_i other represented; cases represented; rfl
  | cons head tail headIH tailIH =>
    rename_i other represented
    cases represented with
    | cons first rest => rw [headIH first, tailIH _ rest]

theorem bindings_core_unique {catalog : SourceCoreDataCatalog.Catalog}
    {binders : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {left right : List Value}
    (first : DataPatternLeaves.BindingsRep catalog binders sources left)
    (second : DataPatternLeaves.BindingsRep catalog binders sources right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons otherHead otherTail => rw [value_core_unique head otherHead, ih otherTail]

/-- The binder bundle already produced by the established matcher theorem has
these exact authenticated payloads, not merely some other typed bundle. -/
theorem Certificate.bindings_typed {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : Certificate compilation source scope site span expected pattern compiled)
    (signatures : context.signatures = compilation.signatures)
    {sourceValue : Dynamic.Value} {value : Value} {bindings : List (TypedBinder × Dynamic.Value)}
    {values : List Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value)
    (matched : Dynamic.PatternMatches context pattern sourceValue bindings)
    (bindingsRepresented : DataPatternLeaves.BindingsRep compilation.checked.catalog compiled.bindings bindings values) :
    BindingsRep compilation.checked.catalog compilation.signatures compiled.bindings bindings values := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures _ _ _ root
  cases matched with
  | intro matchedSource instructionMatch =>
    have arityEq := Dynamic.MatchPatternSourceRepresents.rootArity_eq sourceRep matchedSource
    subst arityEq
    subst instructions
    obtain ⟨typedValues, _, typed⟩ := Tree.binding_types tree _ _ _ _ represented instructionMatch
    have same := bindings_core_unique typed.erase bindingsRepresented
    exact same ▸ typed

end Solcore.SourceSemantics.CoreLowering.DataPatternBindings
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPatternParametricLeaves
/-! Wildcard and binder patterns preserve any relation on source/Core values.
They never inspect a value's representation or clone its captured state. This
lemma is usable for functions, mappings and proxies once the caller's value
relation covers those carriers. It does not establish that relation itself. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternParametricLeaves
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataPatternCertificates DataPatternValues DataPatternExecution

inductive OpaqueLeaf : MatchPatternResolution → Prop where
  | wildcard : OpaqueLeaf .wildcard
  | binder (binder : TypedBinder) : OpaqueLeaf (.binder binder)

inductive BindingsRelated (relation : Dynamic.Value → Value → Prop) :
    List (TypedBinder × Ty) → List (TypedBinder × Dynamic.Value) → List Value → Prop where
  | nil : BindingsRelated relation [] [] []
  | cons {binder : TypedBinder} {type : Ty} {source : Dynamic.Value} {value : Value}
      {binders : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
      (head : relation source value) (tail : BindingsRelated relation binders sources values) :
      BindingsRelated relation ((binder, type) :: binders) ((binder, source) :: sources) (value :: values)

/-- Compiler acceptance preserves the caller's arbitrary value relation through
opaque pattern binding. The source and Core heap/capture identity is untouched. -/
theorem compilePattern_preserves (compilation : Compilation) (compilationFuel : Nat)
    (source : TypedSource) (scope : Scope) (site : StatementId) (span : Syntax.SourceSpan)
    (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : CertifiedPattern compilation.checked.catalog.definitions)
    (accepted : compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : Context) (signatures : context.signatures = compilation.signatures)
    (leaf : OpaqueLeaf pattern.resolution) (relation : Dynamic.Value → Value → Prop)
    {sourceValue : Dynamic.Value} {value : Value} (represented : relation sourceValue value) :
    ∃ bindings values, Dynamic.PatternMatches context pattern sourceValue bindings ∧
      BindingsRelated relation compiled.pattern.bindings bindings values ∧ MatcherRuns compiled.pattern value values := by
  have certificate := certificate_of_compilePattern compilation compilationFuel source scope site span expected pattern compiled accepted
  generalize compiledEq : compiled.pattern = lowered at certificate ⊢
  rcases pattern with ⟨spelling, patternType, resolution, requirements⟩
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context signatures spelling resolution instructions root
  subst instructions
  cases leaf with
  | wildcard =>
    cases tree with
    | wildcard projection =>
      exact ⟨[], [], .intro sourceRep .wildcard, .nil,
        fun _ store _ path => .apply .lambda (path.evaluates store) (.inRight .unit)⟩
  | binder binder =>
    cases tree with
    | binder projection sourceType binderValid =>
      exact ⟨[(binder, sourceValue)], [value], .intro sourceRep .binder, .cons represented .nil,
        fun _ store _ path => .apply .lambda (path.evaluates store) (.inRight (.var rfl))⟩

end Solcore.SourceSemantics.CoreLowering.DataPatternParametricLeaves
end
