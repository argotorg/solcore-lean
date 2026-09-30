import Solcore.SourceSemantics.CoreLowering.DataHeap

/-! Lexical environments for catalog-indexed cells, with explicit internal Core
slots. A match scrutinee gets a mapped source heap cell but no source lexical
binding. Internal slots therefore extend the compiler scope and Core environment
while preserving the source environment. Freshness prevents an internal name
from hiding a source binding. This relation does not make internal IDs readable
source locals merely because the low-level compiler can look them up. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataHeap
open Frontend Frontend.SourceInference GeneralHeap

inductive EnvRepresents (catalog : SourceCoreDataCatalog.Catalog) (mapping : LocationMap)
    (world : Core.StoreTyping) (administrativeContext : Core.Context := []) :
    SourceCoreLocalCell.Scope → Dynamic.Environment → Core.Environment → Prop where
  | nil {administrative : Core.Environment}
      (typed : Core.RuntimeEnvironmentHasTypes world administrative administrativeContext catalog.definitions) :
      EnvRepresents catalog mapping world administrativeContext [] [] administrative
  | cons {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
      {coreEnvironment : Core.Environment} {id : Resolved.LocalId}
      {source : Dynamic.Location} {target : Core.Location} {payload : Core.Ty}
      (reference : ReferenceRepresents mapping world source target payload)
      (tail : EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment) :
      EnvRepresents catalog mapping world administrativeContext ((id, payload) :: scope)
        ((id, source) :: environment)
        (.cellRef (Core.OptionalCell.cellType payload) target :: coreEnvironment)
  | internal {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
      {coreEnvironment : Core.Environment} {id : Resolved.LocalId}
      {source : Dynamic.Location} {target : Core.Location} {payload : Core.Ty}
      (reference : ReferenceRepresents mapping world source target payload)
      (absent : ∀ location, ¬ Dynamic.Environment.LooksUp environment id location)
      (tail : EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment) :
      EnvRepresents catalog mapping world administrativeContext ((id, payload) :: scope) environment
        (.cellRef (Core.OptionalCell.cellType payload) target :: coreEnvironment)

variable {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}

/-- World and location-map extension leave every captured source location and
Core reference unchanged. -/
theorem EnvRepresents.extend {mapping futureMapping : LocationMap} {world futureWorld : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    (related : EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : Core.WorldExtends world futureWorld) :
    EnvRepresents catalog futureMapping futureWorld administrativeContext scope environment coreEnvironment := by
  induction related with
  | nil typed => exact .nil (typed.weaken worlds)
  | cons reference _ ih => exact .cons (reference.extend maps worlds) ih
  | internal reference absent _ ih => exact .internal (reference.extend maps worlds) absent ih

theorem EnvRepresents.runtime_hasTypes {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    (related : EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment) :
    Core.RuntimeEnvironmentHasTypes world coreEnvironment
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) catalog.definitions := by
  induction related with
  | nil typed => exact typed
  | cons reference _ ih => exact .cons (.cellRef reference.typed) ih
  | internal reference _ _ ih => exact .cons (.cellRef reference.typed) ih

/-- Every actual source lexical binding is present at the compiler's first
matching slot, even with internal slots interspersed between lexical scopes. -/
theorem EnvRepresents.lookup_source {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {id : Resolved.LocalId} {location : Dynamic.Location}
    (related : EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment)
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
  | @internal scope environment coreEnvironment other source target payload reference absent tail ih =>
    have different : other ≠ id := by intro same; subst other; exact absent location sourceLookup
    obtain ⟨index, type, found, slot, coreLookup, reference⟩ := ih sourceLookup
    exact ⟨index + 1, type, found, by simp [SourceCoreLocalCell.lookup?, different, slot], coreLookup, reference⟩

/-- A compiler lookup can be used as a source read only with lexical visibility.
This is the deliberate boundary excluding fabricated references to hidden IDs. -/
theorem EnvRepresents.lookup_visible {mapping : LocationMap} {world : Core.StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {id : Resolved.LocalId} {location : Dynamic.Location} {index : Nat} {payload : Core.Ty}
    (related : EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment)
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
    (related : EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment)
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
  exact ⟨.internal reference (environments.fresh_absent fresh)
    (environments.extend ⟨_, rfl⟩ ⟨_, rfl⟩), heapRelated⟩

end Solcore.SourceSemantics.CoreLowering.DataHeap
