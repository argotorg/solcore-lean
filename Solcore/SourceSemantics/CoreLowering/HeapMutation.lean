import Solcore.SourceSemantics.CoreLowering.LocalCell

/-! Structural allocation, mutation and lexical correspondence for the ordinary
scalar/product local-cell profile. Locations are unchanged list indices. These
lemmas exclude generalized cells and mappings through `CellRepresents`; they do
not assert termination or correspondence for the whole source language. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LocalCell

open Frontend Frontend.SourceInference TypeSystem

theorem TypeRepresents.core_unique {sourceType : Ty} {left right : Core.Ty}
    (first : TypeRepresents sourceType left) (second : TypeRepresents sourceType right) :
    left = right := by
  induction first generalizing right with
  | unit | bool | word => cases second; rfl
  | product _ _ leftIH rightIH =>
      cases second with
      | product left right => rw [leftIH left, rightIH right]

theorem TypeRepresents.source_unique {left right : Ty} {coreType : Core.Ty}
    (first : TypeRepresents left coreType) (second : TypeRepresents right coreType) :
    left = right := by
  induction first generalizing right with
  | unit | bool | word => cases second; rfl
  | product _ _ leftIH rightIH =>
      cases second with
      | product left right => rw [leftIH left, rightIH right]

theorem TypeRepresents.cellPayload {sourceType : Ty} {coreType : Core.Ty}
    (types : TypeRepresents sourceType coreType) : Core.CellPayload coreType := by
  induction types with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | product _ _ left right => exact .product left right

theorem CellRepresents.ordinary {cell : Dynamic.Cell} {value : Core.Value} {type : Core.Ty}
    (related : CellRepresents cell value type) : cell.generalized = none := by
  cases related <;> rfl

theorem CellRepresents.rootInitialValue
    {cell : Dynamic.Cell} {value : Core.Value} {type : Core.Ty}
    (related : CellRepresents cell value type) :
    Dynamic.RootInitialValue cell cell.value := by
  cases related with
  | uninitialized types => exact .uninitialized types.not_mapping
  | initialized _ => exact .initialized

theorem HeapRepresents.length_eq {cells : List Dynamic.Cell} {store : Core.Store}
    {world : Core.StoreTyping} (related : HeapRepresents cells store world) :
    cells.length = store.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem HeapRepresents.append {cells more : List Dynamic.Cell} {store extra : Core.Store}
    {world extension : Core.StoreTyping}
    (related : HeapRepresents cells store world)
    (additional : HeapRepresents more extra extension) :
    HeapRepresents (cells ++ more) (store ++ extra) (world ++ extension) := by
  induction related with
  | nil => exact additional
  | cons head _ ih => exact .cons head ih

theorem HeapRepresents.at_world {cells : List Dynamic.Cell} {store : Core.Store}
    {world : Core.StoreTyping} {index : Nat} {type : Core.Ty}
    (related : HeapRepresents cells store world)
    (found : world[index]? = some (Core.OptionalCell.cellType type)) :
    ∃ cell value, Dynamic.Heap.CellAt cells index cell ∧
      store.read? index = some value ∧ CellRepresents cell value type := by
  induction related generalizing index with
  | nil => simp at found
  | @cons cell cells value store payload world head tail ih =>
      cases index with
      | zero =>
          have same : payload = type := by
            simpa [Core.OptionalCell.cellType] using found
          subst payload
          exact ⟨cell, value, .head, rfl, head⟩
      | succ index =>
          obtain ⟨cell, value, selected, read, represents⟩ := ih found
          exact ⟨cell, value, .tail selected, read, represents⟩

/-- This restricted heap also satisfies the older first-order invariant, which
is useful for exact-store weakening. It makes no claim about general heaps. -/
theorem HeapRepresents.firstOrder_hasTypes {cells : List Dynamic.Cell} {store : Core.Store}
    {world : Core.StoreTyping} (related : HeapRepresents cells store world) :
    Core.StoreHasTypes world store where
  length_eq := (related.runtime_hasTypes []).length_eq
  lookup := by
    intro index type found
    induction related generalizing index with
    | nil => simp at found
    | cons head tail ih =>
        cases index with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst type
            exact ⟨_, rfl, .sum .unit head.types.cellPayload,
              (head.runtime_hasType [] []).erase⟩
        | succ index => exact ih found

/-- Source allocation and Core allocation choose exactly the same fresh index. -/
theorem HeapRepresents.allocate {heap after : Dynamic.Heap} {store : Core.Store}
    {world : Core.StoreTyping} {sourceType : Ty} {sourceValue : Option Dynamic.Value}
    {value : Core.Value} {type : Core.Ty} {location : Dynamic.Location}
    (related : HeapRepresents heap.cells store world)
    (cell : CellRepresents { type := sourceType, value := sourceValue } value type)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    location.index = (store.allocate value).2 ∧
      HeapRepresents after.cells (store.allocate value).1
        (world ++ [Core.OptionalCell.cellType type]) ∧
      Core.WorldExtends world (world ++ [Core.OptionalCell.cellType type]) := by
  cases allocated
  exact ⟨related.length_eq, related.append (.cons cell .nil), ⟨_, rfl⟩⟩

theorem HeapRepresents.allocate_uninitialized
    {heap after : Dynamic.Heap} {store : Core.Store} {world : Core.StoreTyping}
    {sourceType : Ty} {type : Core.Ty} {location : Dynamic.Location}
    (related : HeapRepresents heap.cells store world)
    (types : TypeRepresents sourceType type)
    (allocated : Dynamic.Heap.Allocates heap sourceType none location after) :
    location.index = store.length ∧
      HeapRepresents after.cells (store ++ [.inLeft type .unit])
        (world ++ [Core.OptionalCell.cellType type]) := by
  obtain ⟨locationEq, heapRelated, _⟩ := related.allocate (.uninitialized types) allocated
  exact ⟨locationEq, heapRelated⟩

theorem HeapRepresents.allocate_initialized
    {heap after : Dynamic.Heap} {store : Core.Store} {world : Core.StoreTyping}
    {location : Dynamic.Location} (value : SourceStagedValue.Value)
    (related : HeapRepresents heap.cells store world)
    (allocated : Dynamic.Heap.Allocates heap (SourceStagedValue.sourceType value)
      (some (StagedValue.toSource value)) location after) :
    location.index = store.length ∧
      HeapRepresents after.cells (store ++ [.inRight .unit (SourceStagedValue.toCore value)])
        (world ++ [Core.OptionalCell.cellType (SourceStagedValue.coreType value)]) := by
  obtain ⟨locationEq, heapRelated, _⟩ := related.allocate (.initialized value) allocated
  exact ⟨locationEq, heapRelated⟩

/-- Structural source replacement updates the identical Core list position. -/
theorem HeapRepresents.replace {cells updated : List Dynamic.Cell} {store : Core.Store}
    {world : Core.StoreTyping} {index : Nat} {replacement : Dynamic.Cell}
    {value : Core.Value} {type : Core.Ty}
    (related : HeapRepresents cells store world)
    (written : Dynamic.Heap.CellsWrite cells index replacement updated)
    (found : world[index]? = some (Core.OptionalCell.cellType type))
    (newCell : CellRepresents replacement value type) :
    store.write? index value = some (store.set index value) ∧
      HeapRepresents updated (store.set index value) world := by
  induction related generalizing index updated with
  | nil => cases written
  | @cons cell cells old store payload world head tail ih =>
      cases written with
      | head =>
          have same : payload = type := by
            simpa [Core.OptionalCell.cellType] using found
          subst payload
          exact ⟨by simp [Core.Store.write?], .cons newCell tail⟩
      | tail written =>
          obtain ⟨writtenCore, relatedCore⟩ := ih written found
          have bound := (Core.Store.write?_eq_some_iff.mp writtenCore).1
          exact ⟨by simp [Core.Store.write?, Nat.succ_lt_succ bound], .cons head relatedCore⟩

/-- Assignment preserves the declared type and the world; only the selected
optional payload changes. The source write alone does not guarantee its type,
so that obligation is explicit. -/
theorem HeapRepresents.write_initialized
    {heap after : Dynamic.Heap} {store : Core.Store} {world : Core.StoreTyping}
    {location : Dynamic.Location} {previous : Dynamic.Cell}
    (related : HeapRepresents heap.cells store world) (value : SourceStagedValue.Value)
    (read : Dynamic.Heap.Reads heap location previous)
    (sameType : previous.type = SourceStagedValue.sourceType value)
    (written : Dynamic.Heap.Writes heap location (some (StagedValue.toSource value)) after) :
    store.write? location.index (.inRight .unit (SourceStagedValue.toCore value)) =
        some (store.set location.index (.inRight .unit (SourceStagedValue.toCore value))) ∧
      HeapRepresents after.cells
        (store.set location.index (.inRight .unit (SourceStagedValue.toCore value))) world := by
  cases written with
  | @intro old updated oldRead replaced =>
      have same := read.functional oldRead
      subst old
      obtain ⟨oldValue, type, _, found, represents⟩ := related.read read
      have types := represents.types
      rw [sameType] at types
      have coreType := types.core_unique (stagedTypes value)
      subst type
      have ordinary := represents.ordinary
      have cellEq : { previous with value := some (StagedValue.toSource value) } =
          ({ type := SourceStagedValue.sourceType value, value := some (StagedValue.toSource value) } :
            Dynamic.Cell) := by
        cases previous
        simp_all
      apply related.replace replaced found
      rw [cellEq]
      exact .initialized value

/-- Lexical positions share source identities and stable heap locations; the
world proves that every stored reference has the scope's optional payload type. -/
inductive EnvRepresents (world : Core.StoreTyping) :
    SourceCoreLocalCell.Scope → Dynamic.Environment → Core.Environment → Prop where
  | nil : EnvRepresents world [] [] []
  | cons {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
      {coreEnvironment : Core.Environment} {id : Resolved.LocalId}
      {location : Dynamic.Location} {type : Core.Ty}
      (found : world[location.index]? = some (Core.OptionalCell.cellType type))
      (tail : EnvRepresents world scope environment coreEnvironment) :
      EnvRepresents world ((id, type) :: scope) ((id, location) :: environment)
        (.cellRef (Core.OptionalCell.cellType type) location.index :: coreEnvironment)

theorem EnvRepresents.extend {world future : Core.StoreTyping}
    {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
    {coreEnvironment : Core.Environment}
    (related : EnvRepresents world scope environment coreEnvironment)
    (extended : Core.WorldExtends world future) :
    EnvRepresents future scope environment coreEnvironment := by
  induction related with
  | nil => exact .nil
  | cons found _ ih => exact .cons (extended.lookup found) ih

theorem EnvRepresents.runtime_hasTypes {world : Core.StoreTyping}
    {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
    {coreEnvironment : Core.Environment}
    (related : EnvRepresents world scope environment coreEnvironment)
    (definitions : Core.DataEnvironment) :
    Core.RuntimeEnvironmentHasTypes world coreEnvironment
      (SourceCoreLocalCell.coreContext scope) definitions := by
  induction related with
  | nil => exact .nil
  | cons found _ ih => exact .cons (.cellRef found) ih

/-- Both lookups use the first matching identity, including shadowed identities. -/
theorem EnvRepresents.lookup {world : Core.StoreTyping}
    {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
    {coreEnvironment : Core.Environment} {id : Resolved.LocalId}
    {index : Nat} {type : Core.Ty}
    (related : EnvRepresents world scope environment coreEnvironment)
    (slot : SourceCoreLocalCell.lookup? scope id = some (index, type)) :
    ∃ location, Dynamic.Environment.LooksUp environment id location ∧
      coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType type) location.index) ∧
      world[location.index]? = some (Core.OptionalCell.cellType type) := by
  induction related generalizing index with
  | nil => simp [SourceCoreLocalCell.lookup?] at slot
  | @cons scope environment coreEnvironment other location payload found tail ih =>
      by_cases same : other = id
      · simp [SourceCoreLocalCell.lookup?, same] at slot
        rcases slot with ⟨rfl, rfl⟩
        subst other
        exact ⟨location, .head, rfl, found⟩
      · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at slot
        cases lookup : SourceCoreLocalCell.lookup? scope id with
        | none => simp [lookup] at slot
        | some pair =>
            rcases pair with ⟨previous, foundType⟩
            simp only [lookup, Option.map_some, Option.some.injEq, Prod.mk.injEq] at slot
            rcases slot with ⟨rfl, rfl⟩
            obtain ⟨location, sourceLookup, coreLookup, worldLookup⟩ := ih lookup
            exact ⟨location, .tail same sourceLookup, coreLookup, worldLookup⟩

theorem EnvRepresents.lookup_heap {heap : Dynamic.Heap} {store : Core.Store}
    {world : Core.StoreTyping} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {id : Resolved.LocalId} {index : Nat} {type : Core.Ty}
    (environmentRelated : EnvRepresents world scope environment coreEnvironment)
    (heapRelated : HeapRepresents heap.cells store world)
    (slot : SourceCoreLocalCell.lookup? scope id = some (index, type)) :
    ∃ location cell value, Dynamic.Environment.LooksUp environment id location ∧
      coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType type) location.index) ∧
      world[location.index]? = some (Core.OptionalCell.cellType type) ∧
      Dynamic.Heap.Reads heap location cell ∧ store.read? location.index = some value ∧
      CellRepresents cell value type := by
  obtain ⟨location, sourceLookup, coreLookup, found⟩ := environmentRelated.lookup slot
  obtain ⟨cell, value, selected, read, represents⟩ := heapRelated.at_world found
  exact ⟨location, cell, value, sourceLookup, coreLookup, found, .intro selected, read, represents⟩

theorem EnvRepresents.bind {heap after : Dynamic.Heap} {store : Core.Store}
    {world : Core.StoreTyping} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {id : Resolved.LocalId} {sourceType : Ty} {sourceValue : Option Dynamic.Value}
    {value : Core.Value} {type : Core.Ty} {location : Dynamic.Location}
    (environmentRelated : EnvRepresents world scope environment coreEnvironment)
    (heapRelated : HeapRepresents heap.cells store world)
    (cell : CellRepresents { type := sourceType, value := sourceValue } value type)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    EnvRepresents (world ++ [Core.OptionalCell.cellType type])
      ((id, type) :: scope) ((id, location) :: environment)
      (.cellRef (Core.OptionalCell.cellType type) location.index :: coreEnvironment) ∧
      HeapRepresents after.cells (store.allocate value).1
        (world ++ [Core.OptionalCell.cellType type]) := by
  obtain ⟨index, allocatedHeap, extension⟩ := heapRelated.allocate cell allocated
  refine ⟨.cons ?_ (environmentRelated.extend extension), allocatedHeap⟩
  have lengthEq := (heapRelated.runtime_hasTypes []).length_eq
  rw [index]
  change (world ++ [Core.OptionalCell.cellType type])[store.length]? = _
  rw [← lengthEq]
  simp

private theorem cellsWrite_set {cells : List Dynamic.Cell} {index : Nat}
    {previous : Dynamic.Cell} (selected : Dynamic.Heap.CellAt cells index previous)
    (replacement : Dynamic.Cell) :
    Dynamic.Heap.CellsWrite cells index replacement (cells.set index replacement) := by
  induction selected with
  | head => exact .head
  | tail _ ih => exact .tail ih

/-- Resolve a bare local before the RHS, then replace its value in the latest
RHS heap. Existing aliases keep their location and see the replacement. The
world extension accounts for allocations performed by the RHS. -/
theorem equal_assignment
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {before rhsHeap : Dynamic.Heap} {store rhsStore : Core.Store}
    {world rhsWorld : Core.StoreTyping} {target : PlaceResolution}
    {rhs : ExpressionId} {index : Nat} {payloadType : Core.Ty}
    (environmentRelated : EnvRepresents world scope environment coreEnvironment)
    (heapRelated : HeapRepresents before.cells store world)
    (extended : Core.WorldExtends world rhsWorld)
    (rhsRelated : HeapRepresents rhsHeap.cells rhsStore rhsWorld)
    (slot : SourceCoreLocalCell.lookup? scope target.root = some (index, payloadType))
    (bare : target.projections = []) (value : SourceStagedValue.Value)
    (valueType : SourceStagedValue.coreType value = payloadType)
    (rhsEvaluated : Dynamic.ExpressionEvaluates program context evidence source environment
      before rhs (StagedValue.toSource value) rhsHeap) :
    ∃ (location : Dynamic.Location) (after : Dynamic.Heap) (finalStore : Core.Store),
      Dynamic.SourcePlaceAssignment program context evidence source
        (Dynamic.AssignmentValueApplies .equal) environment before target rhs
        (StagedValue.toSource value) after ∧
      coreEnvironment[index]? =
        some (.cellRef (Core.OptionalCell.cellType payloadType) location.index) ∧
      (∃ oldValue, rhsStore.read? location.index = some oldValue) ∧
      rhsStore.write? location.index (.inRight .unit (SourceStagedValue.toCore value)) =
        some finalStore ∧
      HeapRepresents after.cells finalStore rhsWorld ∧
      EnvRepresents rhsWorld scope environment coreEnvironment := by
  obtain ⟨location, initialCell, initialValue, sourceLookup, coreLookup, found,
      initialRead, _, initialRepresents⟩ := environmentRelated.lookup_heap heapRelated slot
  obtain ⟨currentCell, currentValue, currentAt, currentCoreRead, currentRepresents⟩ :=
    rhsRelated.at_world (extended.lookup found)
  have currentRead : Dynamic.Heap.Reads rhsHeap location currentCell := .intro currentAt
  have sameType : currentCell.type = initialCell.type :=
    currentRepresents.types.source_unique initialRepresents.types
  have writtenType : currentCell.type = SourceStagedValue.sourceType value := by
    apply currentRepresents.types.source_unique
    rw [← valueType]
    exact stagedTypes value
  let replacement : Dynamic.Cell :=
    { currentCell with value := some (StagedValue.toSource value) }
  let after : Dynamic.Heap := ⟨rhsHeap.cells.set location.index replacement⟩
  have sourceWrite : Dynamic.Heap.Writes rhsHeap location
      (some (StagedValue.toSource value)) after :=
    .intro currentRead (cellsWrite_set currentAt replacement)
  obtain ⟨coreWrite, updatedRelated⟩ := rhsRelated.write_initialized value currentRead
    writtenType sourceWrite
  refine ⟨location, after, _, ?_, coreLookup, ⟨currentValue, currentCoreRead⟩,
    coreWrite, updatedRelated, environmentRelated.extend extended⟩
  let captured : Dynamic.ResolvedPlace := {
    location := location
    rootType := initialCell.type
    valueType := target.type
    projections := []
    selected := initialCell.value
  }
  have resolved : Dynamic.SourcePlaceResolves program context evidence source environment
      before target captured before := by
    apply Dynamic.SourcePlaceResolves.intro sourceLookup initialRead
    · rw [bare]
      exact .nil
    · exact initialRead
    · exact initialRepresents.rootInitialValue
    · exact .nil
  exact .intro resolved rhsEvaluated
    (.intro currentRead sameType currentRepresents.rootInitialValue
      (.leaf (.equal initialCell.value (StagedValue.toSource value))) sourceWrite)

end Solcore.SourceSemantics.CoreLowering.LocalCell
