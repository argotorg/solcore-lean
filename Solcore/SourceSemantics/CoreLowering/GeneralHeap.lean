import Solcore.SourceSemantics.CoreLowering.HeapMutation

/-! A source location maps to an independently allocated Core location.

Mapped cells currently contain ordinary scalar/product optional values. Extra
Core cells are administrative and may contain any runtime-typed value,
including closures and references. The finite Core world types references by
lookup; none of these relations recursively traverses a referenced store.
This is a representation and mutation foundation, not closure-body semantic
preservation or a representation of generalized source cells and mappings.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.GeneralHeap

open Frontend Frontend.SourceInference TypeSystem

/-- Indexed by the source heap location. Entries are stable Core locations;
administrative Core cells have no entry. -/
abbrev LocationMap := List Core.Location

namespace LocationMap

def Injective (mapping : LocationMap) : Prop :=
  ∀ {left right target : Nat}, mapping[left]? = some target →
    mapping[right]? = some target → left = right

def Extends (initial future : LocationMap) : Prop :=
  ∃ suffix, future = initial ++ suffix

theorem Extends.refl (mapping : LocationMap) : Extends mapping mapping := ⟨[], by simp⟩

theorem Extends.trans {first second third : LocationMap}
    (left : Extends first second) (right : Extends second third) : Extends first third := by
  obtain ⟨middle, rfl⟩ := left
  obtain ⟨last, rfl⟩ := right
  exact ⟨middle ++ last, by simp [List.append_assoc]⟩

theorem Extends.length_le {initial future : LocationMap} (extension : Extends initial future) :
    initial.length ≤ future.length := by
  obtain ⟨suffix, rfl⟩ := extension
  simp

theorem Extends.lookup {initial future : LocationMap} (extension : Extends initial future)
    {source target : Nat} (found : initial[source]? = some target) :
    future[source]? = some target := by
  obtain ⟨suffix, rfl⟩ := extension
  rw [List.getElem?_append_left ((List.getElem?_eq_some_iff.mp found).1)]
  exact found

private theorem append_lookup {mapping : LocationMap} {fresh index target : Nat}
    (found : (mapping ++ [fresh])[index]? = some target) :
    mapping[index]? = some target ∨ (index = mapping.length ∧ target = fresh) := by
  by_cases old : index < mapping.length
  · left
    rwa [List.getElem?_append_left old] at found
  · right
    have bound := (List.getElem?_eq_some_iff.mp found).1
    have indexEq : index = mapping.length := by simp only [List.length_append, List.length_singleton] at bound; omega
    subst index
    exact ⟨rfl, by simpa using found.symm⟩

theorem Injective.append {mapping : LocationMap} (injective : Injective mapping)
    (fresh : Core.Location) (absent : ∀ {index : Nat}, mapping[index]? ≠ some fresh) :
    Injective (mapping ++ [fresh]) := by
  intro left right target leftFound rightFound
  rcases append_lookup leftFound with leftOld | ⟨leftEq, targetEq⟩
  · rcases append_lookup rightFound with rightOld | ⟨rightEq, targetEq⟩
    · exact injective leftOld rightOld
    · exact (absent (targetEq ▸ leftOld)).elim
  · rcases append_lookup rightFound with rightOld | ⟨rightEq, _⟩
    · exact (absent (targetEq ▸ rightOld)).elim
    · exact leftEq.trans rightEq.symm

end LocationMap

/-- A reference points to the mapped location and carries the world's exact
optional payload type. Reading it need not inspect the heap to type it. -/
structure ReferenceRepresents (mapping : LocationMap) (world : Core.StoreTyping)
    (source : Dynamic.Location) (target : Core.Location) (payload : Core.Ty) : Prop where
  mapped : mapping[source.index]? = some target
  typed : world[target]? = some (Core.OptionalCell.cellType payload)

theorem ReferenceRepresents.extend {mapping futureMapping : LocationMap}
    {world futureWorld : Core.StoreTyping} {source : Dynamic.Location}
    {target : Core.Location} {payload : Core.Ty}
    (related : ReferenceRepresents mapping world source target payload)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : Core.WorldExtends world futureWorld) :
    ReferenceRepresents futureMapping futureWorld source target payload :=
  ⟨maps.lookup related.mapped, worlds.lookup related.typed⟩

theorem ReferenceRepresents.runtime_hasType {mapping : LocationMap} {world : Core.StoreTyping}
    {source : Dynamic.Location} {target : Core.Location} {payload : Core.Ty}
    (related : ReferenceRepresents mapping world source target payload) :
    Core.RuntimeValueHasType world (.cellRef (Core.OptionalCell.cellType payload) target)
      (Core.OptionalCell.referenceType payload) := .cellRef related.typed

/-- The scalar/product part of the value relation is valid in every world.
References held by environments use `ReferenceRepresents` separately, because
the source value carrier has no raw reference constructor. -/
inductive ValueRepresents (mapping : LocationMap) (world : Core.StoreTyping) :
    Dynamic.Value → Core.Value → Ty → Core.Ty → Prop where
  | scalar (value : SourceStagedValue.Value) :
      ValueRepresents mapping world (StagedValue.toSource value) (SourceStagedValue.toCore value)
        (SourceStagedValue.sourceType value) (SourceStagedValue.coreType value)

theorem ValueRepresents.extend {mapping futureMapping : LocationMap}
    {world futureWorld : Core.StoreTyping} {source : Dynamic.Value} {target : Core.Value}
    {sourceType : Ty} {targetType : Core.Ty}
    (related : ValueRepresents mapping world source target sourceType targetType)
    (_maps : LocationMap.Extends mapping futureMapping) (_worlds : Core.WorldExtends world futureWorld) :
    ValueRepresents futureMapping futureWorld source target sourceType targetType := by
  cases related with
  | scalar value => exact .scalar value

theorem ValueRepresents.runtime_hasType {mapping : LocationMap} {world : Core.StoreTyping}
    {source : Dynamic.Value} {target : Core.Value} {sourceType : Ty} {targetType : Core.Ty}
    (related : ValueRepresents mapping world source target sourceType targetType) :
    Core.RuntimeValueHasType world target targetType := by
  cases related with
  | scalar value =>
      induction value with
      | unit => exact .unit
      | bool => exact .bool
      | word => exact .word
      | product _ _ left right => exact .pair left right

/-- Every source cell is mapped injectively. The entire Core store, including
unmapped administrative cells, satisfies general runtime world typing. -/
structure HeapRepresents (mapping : LocationMap) (world : Core.StoreTyping)
    (heap : Dynamic.Heap) (store : Core.Store) : Prop where
  length_eq : mapping.length = heap.cells.length
  injective : LocationMap.Injective mapping
  runtime_hasTypes : Core.RuntimeStoreHasTypes world store
  cells : ∀ {source target : Nat}, mapping[source]? = some target →
    ∃ cell value payload,
      Dynamic.Heap.Reads heap ⟨source⟩ cell ∧
      world[target]? = some (Core.OptionalCell.cellType payload) ∧
      store.read? target = some value ∧ LocalCell.CellRepresents cell value payload

theorem HeapRepresents.empty : HeapRepresents [] [] ⟨[]⟩ [] := by
  refine ⟨rfl, ?_, .nil, ?_⟩
  · intro left right target impossible; simp at impossible
  · intro source target impossible; simp at impossible

theorem HeapRepresents.target_lt {mapping : LocationMap} {world : Core.StoreTyping}
    {heap : Dynamic.Heap} {store : Core.Store} (related : HeapRepresents mapping world heap store)
    {source target : Nat} (mapped : mapping[source]? = some target) : target < store.length := by
  obtain ⟨_, _, _, _, typed, _, _⟩ := related.cells mapped
  exact related.runtime_hasTypes.location_lt typed

theorem HeapRepresents.read {mapping : LocationMap} {world : Core.StoreTyping}
    {heap : Dynamic.Heap} {store : Core.Store} (related : HeapRepresents mapping world heap store)
    {location : Dynamic.Location} {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads heap location cell) :
    ∃ target value payload,
      ReferenceRepresents mapping world location target payload ∧
      store.read? target = some value ∧ LocalCell.CellRepresents cell value payload := by
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
    (related : HeapRepresents mapping world heap store) {value : Core.Value} {type : Core.Ty}
    (typed : Core.RuntimeValueHasType world value type) :
    HeapRepresents mapping (world ++ [type]) heap (store.allocate value).1 := by
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
    (related : HeapRepresents mapping world heap store)
    (cell : LocalCell.CellRepresents { type := sourceType, value := sourceValue } value payload)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    HeapRepresents (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
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
    related.runtime_hasTypes.allocate (cell.runtime_hasType world []), ?_⟩, ⟨freshMap, freshType⟩⟩
  · simp [related.length_eq]
  · intro index impossible
    have bound := related.target_lt impossible
    omega
  · intro source target mapped
    rcases LocationMap.append_lookup mapped with old | ⟨sourceEq, targetEq⟩
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
    (related : HeapRepresents mapping world heap store)
    (absent : ∀ {source : Nat}, mapping[source]? ≠ some location)
    (found : world[location]? = some type) (typed : Core.RuntimeValueHasType world value type)
    (written : store.write? location value = some updated) :
    HeapRepresents mapping world heap updated := by
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
    (related : HeapRepresents mapping world heap store)
    (reference : ReferenceRepresents mapping world location target payload)
    (written : Dynamic.Heap.CellsWrite heap.cells location.index replacement after.cells)
    (newCell : LocalCell.CellRepresents replacement value payload) :
    ∃ updated, store.write? target value = some updated ∧
      HeapRepresents mapping world after updated := by
  obtain ⟨updated, coreWritten⟩ := related.runtime_hasTypes.write_exists (value := value) reference.typed
  refine ⟨updated, coreWritten, ⟨related.length_eq.trans written.length_eq.symm,
    related.injective, related.runtime_hasTypes.write reference.typed
      (newCell.runtime_hasType world []) coreWritten, ?_⟩⟩
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

/-- A source value write preserves the selected declaration's type, every
alias, the location map, and the Core world. -/
theorem HeapRepresents.write_initialized
    {mapping : LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap} {store : Core.Store}
    {location : Dynamic.Location} {target : Core.Location} {payload : Core.Ty}
    (related : HeapRepresents mapping world heap store)
    (reference : ReferenceRepresents mapping world location target payload)
    (value : SourceStagedValue.Value) (valueType : SourceStagedValue.coreType value = payload)
    (written : Dynamic.Heap.Writes heap location (some (StagedValue.toSource value)) after) :
    ∃ updated, store.write? target (.inRight .unit (SourceStagedValue.toCore value)) = some updated ∧
      HeapRepresents mapping world after updated := by
  cases written with
  | @intro previous cells read written =>
      obtain ⟨cell, old, oldType, oldRead, found, _, represents⟩ := related.cells reference.mapped
      have same := read.functional oldRead
      subst cell
      have typeEq : oldType = payload := by
        simpa [Core.OptionalCell.cellType] using Option.some.inj (found.symm.trans reference.typed)
      subst oldType
      have sourceType : previous.type = SourceStagedValue.sourceType value :=
        represents.types.source_unique (valueType ▸ LocalCell.stagedTypes value)
      have ordinary := represents.ordinary
      have replacementEq : { previous with value := some (StagedValue.toSource value) } =
          ({ type := SourceStagedValue.sourceType value, value := some (StagedValue.toSource value) } : Dynamic.Cell) := by
        cases previous
        simp_all
      apply related.replace reference written
      rw [replacementEq, ← valueType]
      exact .initialized value

private theorem source_cell_exists {cells : List Dynamic.Cell} {index : Nat}
    (bound : index < cells.length) : ∃ cell, Dynamic.Heap.CellAt cells index cell := by
  induction cells generalizing index with
  | nil => simp at bound
  | cons head tail ih =>
      cases index with
      | zero => exact ⟨head, .head⟩
      | succ index =>
          obtain ⟨cell, selected⟩ := ih (by simpa using bound)
          exact ⟨cell, .tail selected⟩

/-- The established exact-index heap representation embeds into this relation
with the identity map, without changing any previous theorem. -/
theorem HeapRepresents.of_exact {heap : Dynamic.Heap} {store : Core.Store} {world : Core.StoreTyping}
    (related : LocalCell.HeapRepresents heap.cells store world) :
    HeapRepresents (List.range heap.cells.length) world heap store := by
  refine ⟨by simp, ?_, related.runtime_hasTypes [], ?_⟩
  · intro left right target leftFound rightFound
    have leftBound : left < heap.cells.length := by simpa using (List.getElem?_eq_some_iff.mp leftFound).1
    have rightBound : right < heap.cells.length := by simpa using (List.getElem?_eq_some_iff.mp rightFound).1
    rw [List.getElem?_range leftBound] at leftFound
    rw [List.getElem?_range rightBound] at rightFound
    exact (Option.some.inj leftFound).trans (Option.some.inj rightFound).symm
  · intro source target mapped
    have sourceBound : source < heap.cells.length := by simpa using (List.getElem?_eq_some_iff.mp mapped).1
    rw [List.getElem?_range sourceBound] at mapped
    have same := Option.some.inj mapped
    subst target
    obtain ⟨cell, selected⟩ := source_cell_exists sourceBound
    obtain ⟨value, payload, read, typed, cellRelated⟩ := related.at selected
    exact ⟨cell, value, payload, .intro selected, typed, read, cellRelated⟩

/-- Captures contain locations, not recursively copied cell values. The tail
can contain typed administrative captures (for example, global function refs).
Payload types here may be higher order even though `HeapRepresents` currently
restricts mapped source cells to the scalar/product fragment. -/
inductive EnvRepresents (mapping : LocationMap) (world : Core.StoreTyping)
    (administrativeContext : Core.Context := []) :
    SourceCoreLocalCell.Scope → Dynamic.Environment → Core.Environment → Prop where
  | nil {administrative : Core.Environment}
      (typed : Core.RuntimeEnvironmentHasTypes world administrative administrativeContext) :
      EnvRepresents mapping world administrativeContext [] [] administrative
  | cons {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
      {coreEnvironment : Core.Environment} {id : Resolved.LocalId}
      {source : Dynamic.Location} {target : Core.Location} {payload : Core.Ty}
      (reference : ReferenceRepresents mapping world source target payload)
      (tail : EnvRepresents mapping world administrativeContext scope environment coreEnvironment) :
      EnvRepresents mapping world administrativeContext ((id, payload) :: scope)
        ((id, source) :: environment)
        (.cellRef (Core.OptionalCell.cellType payload) target :: coreEnvironment)

theorem EnvRepresents.extend {mapping futureMapping : LocationMap} {world futureWorld : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    (related : EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : Core.WorldExtends world futureWorld) :
    EnvRepresents futureMapping futureWorld administrativeContext scope environment coreEnvironment := by
  induction related with
  | nil typed => exact .nil (typed.weaken worlds)
  | cons reference _ ih => exact .cons (reference.extend maps worlds) ih

theorem EnvRepresents.runtime_hasTypes {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    (related : EnvRepresents mapping world administrativeContext scope environment coreEnvironment) :
    Core.RuntimeEnvironmentHasTypes world coreEnvironment
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) := by
  induction related with
  | nil typed => exact typed
  | cons reference _ ih => exact .cons reference.runtime_hasType ih

/-- First-match lexical lookup selects the same mapped cell on both sides,
including when a newer binding shadows an older identity. -/
theorem EnvRepresents.lookup {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {id : Resolved.LocalId} {index : Nat} {payload : Core.Ty}
    (related : EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (slot : SourceCoreLocalCell.lookup? scope id = some (index, payload)) :
    ∃ source target, Dynamic.Environment.LooksUp environment id source ∧
      coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType payload) target) ∧
      ReferenceRepresents mapping world source target payload := by
  induction related generalizing index with
  | nil => simp [SourceCoreLocalCell.lookup?] at slot
  | @cons scope environment coreEnvironment other source target type reference tail ih =>
      by_cases same : other = id
      · simp [SourceCoreLocalCell.lookup?, same] at slot
        rcases slot with ⟨rfl, rfl⟩
        subst other
        exact ⟨source, target, .head, rfl, reference⟩
      · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at slot
        cases found : SourceCoreLocalCell.lookup? scope id with
        | none => simp [found] at slot
        | some pair =>
            rcases pair with ⟨previous, foundType⟩
            simp only [found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at slot
            rcases slot with ⟨rfl, rfl⟩
            obtain ⟨source, target, sourceLookup, coreLookup, reference⟩ := ih found
            exact ⟨source, target, .tail same sourceLookup, coreLookup, reference⟩

theorem EnvRepresents.lookup_heap {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {heap : Dynamic.Heap} {store : Core.Store} {id : Resolved.LocalId} {index : Nat} {payload : Core.Ty}
    (environments : EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents mapping world heap store)
    (slot : SourceCoreLocalCell.lookup? scope id = some (index, payload)) :
    ∃ source target cell value,
      Dynamic.Environment.LooksUp environment id source ∧
      coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType payload) target) ∧
      ReferenceRepresents mapping world source target payload ∧
      Dynamic.Heap.Reads heap source cell ∧ store.read? target = some value ∧
      LocalCell.CellRepresents cell value payload := by
  obtain ⟨source, target, sourceLookup, coreLookup, reference⟩ := environments.lookup slot
  obtain ⟨cell, value, type, sourceRead, found, coreRead, represents⟩ := heaps.cells reference.mapped
  have same : type = payload := by
    simpa [Core.OptionalCell.cellType] using Option.some.inj (found.symm.trans reference.typed)
  subst type
  exact ⟨source, target, cell, value, sourceLookup, coreLookup, reference, sourceRead, coreRead, represents⟩

/-- Binding a newly allocated source cell uses the independent fresh Core
location, and transports every existing captured reference through extension. -/
theorem EnvRepresents.bind {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {heap after : Dynamic.Heap} {store : Core.Store} {id : Resolved.LocalId}
    {sourceType : Ty} {sourceValue : Option Dynamic.Value} {location : Dynamic.Location}
    {value : Core.Value} {payload : Core.Ty}
    (environments : EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents mapping world heap store)
    (cell : LocalCell.CellRepresents { type := sourceType, value := sourceValue } value payload)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    EnvRepresents (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      administrativeContext ((id, payload) :: scope) ((id, location) :: environment)
      (.cellRef (Core.OptionalCell.cellType payload) store.length :: coreEnvironment) ∧
    HeapRepresents (mapping ++ [store.length]) (world ++ [Core.OptionalCell.cellType payload])
      after (store.allocate value).1 := by
  obtain ⟨heapRelated, reference⟩ := heaps.allocate cell allocated
  exact ⟨.cons reference (environments.extend ⟨_, rfl⟩ ⟨_, rfl⟩), heapRelated⟩

/-- Every newly allocated Core location is outside the current source map. -/
theorem HeapRepresents.fresh_unmapped {mapping : LocationMap} {world : Core.StoreTyping}
    {heap : Dynamic.Heap} {store : Core.Store} (related : HeapRepresents mapping world heap store) :
    ∀ {source : Nat}, mapping[source]? ≠ some store.length := by
  intro source found
  have bound := related.target_lt found
  omega

/-- A local read uses the source location in its semantic fault and the mapped
Core location for the load. Administrative cells never appear in that source
fault, and reading a mapped scalar cell does not require a first-order store. -/
theorem read_preserves {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {payload : Core.Ty}
    (site : LocalCell.ReadSite source scope id payload)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store}
    (environments : EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents mapping world heap store) (reason : Core.Word) :
    ∃ location target sourceOutcome coreValue,
      ReferenceRepresents mapping world location target payload ∧
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      LocalCell.OutcomeRepresents location reason sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store (Core.OptionalCell.read payload (.var site.index) reason) coreValue store := by
  obtain ⟨location, target, cell, value, sourceLookup, coreLookup, reference, sourceRead, coreRead, represents⟩ :=
    environments.lookup_heap heaps site.slot
  cases represents with
  | uninitialized types =>
      refine ⟨location, target, _, _, reference, .fault ?_, .uninitialized payload,
        Core.OptionalCell.read_failure reason (.var coreLookup) coreRead⟩
      apply Dynamic.ExpressionFaults.form site.contains
      rw [site.form, site.requirements, site.coercions]
      exact .localUninitialized (owned := []) rfl sourceLookup sourceRead rfl rfl types.not_mapping
  | initialized value =>
      refine ⟨location, target, _, _, reference, .value ?_, .initialized value,
        Core.OptionalCell.read_success reason (.var coreLookup) coreRead⟩
      apply Dynamic.ExpressionEvaluates.intro site.contains
      · rw [site.form, site.requirements, site.coercions]
        exact .local rfl sourceLookup sourceRead rfl rfl
      · rw [site.coercions]; exact .nil

/-- The existing executable local-read lowerer works with the new mapping.
All completed Core runs agree with the independently derived source outcome. -/
theorem read_lower_run_preserves {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {payload : Core.Ty}
    (site : LocalCell.ReadSite source scope id payload) (unique : NodeOccurrencesUnique source)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store}
    (environments : EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents mapping world heap store) (reason : Core.Word) :
    ∃ location target expression sourceOutcome coreValue required,
      SourceCoreLocalCell.lowerRead source scope id reason = .ok expression ∧
      ReferenceRepresents mapping world location target payload ∧
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      LocalCell.OutcomeRepresents location reason sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial expression coreEnvironment store) =
        .done coreValue store) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial expression coreEnvironment store) =
        .done actual actualStore → actual = coreValue ∧ actualStore = store) := by
  obtain ⟨location, target, outcome, value, reference, sourceEvaluation, represented, coreEvaluation⟩ :=
    read_preserves site program context evidence environments heaps reason
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel coreEvaluation
  refine ⟨location, target, _, outcome, value, required, site.lower unique reason, reference,
    sourceEvaluation, represented, completes, ?_⟩
  intro fuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreEvaluation

end Solcore.SourceSemantics.CoreLowering.GeneralHeap
