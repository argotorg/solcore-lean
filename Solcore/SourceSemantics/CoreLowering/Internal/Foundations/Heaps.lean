import Solcore.Frontend.SourceCore.Lowering
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LiteralsAndStagedValues
import Solcore.SourceSemantics.Dynamic.Fault
import Solcore.Core.Internal.MappingLaws
import Solcore.SourceSemantics.Dynamic.Primitive
import Solcore.Core.Internal.Renaming

/-!
# Heaps

`GeneralHeap`, location maps from Source to Core, with heap frames and mutation, ordered and word mappings, local cells and the renaming of heap effects.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LocalCell
/-!
The optional-cell representation of ordinary scalar/product source locals.

Heap correspondence is structural and includes uninitialized cells. The local
read lemmas connect actual executable lowering to independent successful and
faulting source derivations. They do not execute the typed-source runtime or
assume its answer. Mapping auto-initialization and generalized descriptors are
outside this representation.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LocalCell

open Frontend Frontend.SourceInference TypeSystem

inductive TypeRepresents : Ty → Core.Ty → Prop where
  | unit : TypeRepresents .unit .unit
  | bool : TypeRepresents .bool .bool
  | word : TypeRepresents .word .word
  | product {left right : Ty} {coreLeft coreRight : Core.Ty}
      (leftTypes : TypeRepresents left coreLeft)
      (rightTypes : TypeRepresents right coreRight) :
      TypeRepresents (.product left right) (.product coreLeft coreRight)

theorem TypeRepresents.lower {sourceType : Ty} {coreType : Core.Ty}
    (types : TypeRepresents sourceType coreType)
    (site : SourceCoreElaboration.ErrorSite) :
    SourceCoreElaboration.lowerType site sourceType = .ok coreType := by
  induction types with
  | unit | bool | word => rfl
  | product _ _ left right => exact SourceCoreElaboration.lowerType_product left right

theorem TypeRepresents.wellFormed {sourceType : Ty} {coreType : Core.Ty}
    (types : TypeRepresents sourceType coreType) (definitions : Core.DataEnvironment) :
    Core.Ty.WellFormed definitions coreType := by
  induction types with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | product _ _ left right => exact .product left right

theorem TypeRepresents.not_mapping {sourceType : Ty} {coreType : Core.Ty}
    (types : TypeRepresents sourceType coreType) :
    ¬ ∃ keyType valueType, sourceType = .mapping keyType valueType := by
  cases types <;> rintro ⟨_, _, impossible⟩ <;> cases impossible

theorem stagedTypes (value : SourceStagedValue.Value) :
    TypeRepresents (SourceStagedValue.sourceType value) (SourceStagedValue.coreType value) := by
  induction value with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | product _ _ left right => exact .product left right

inductive CellRepresents : Dynamic.Cell → Core.Value → Core.Ty → Prop where
  | uninitialized {sourceType : Ty} {coreType : Core.Ty}
      (types : TypeRepresents sourceType coreType) :
      CellRepresents { type := sourceType, value := none }
        (.inLeft coreType .unit) coreType
  | initialized (value : SourceStagedValue.Value) :
      CellRepresents
        { type := SourceStagedValue.sourceType value, value := some (StagedValue.toSource value) }
        (.inRight .unit (SourceStagedValue.toCore value)) (SourceStagedValue.coreType value)

theorem CellRepresents.types {cell : Dynamic.Cell} {value : Core.Value} {type : Core.Ty}
    (related : CellRepresents cell value type) : TypeRepresents cell.type type := by
  cases related with
  | uninitialized types => exact types
  | initialized value => exact stagedTypes value

/-- The Core world records each optional payload's type at the same index. -/
inductive HeapRepresents : List Dynamic.Cell → Core.Store → Core.StoreTyping → Prop where
  | nil : HeapRepresents [] [] []
  | cons {cell : Dynamic.Cell} {cells : List Dynamic.Cell}
      {value : Core.Value} {store : Core.Store} {type : Core.Ty} {world : Core.StoreTyping}
      (head : CellRepresents cell value type)
      (tail : HeapRepresents cells store world) :
      HeapRepresents (cell :: cells) (value :: store)
        (Core.OptionalCell.cellType type :: world)

theorem HeapRepresents.at {cells : List Dynamic.Cell} {store : Core.Store}
    {world : Core.StoreTyping} {index : Nat} {cell : Dynamic.Cell}
    (related : HeapRepresents cells store world)
    (selected : Dynamic.Heap.CellAt cells index cell) :
    ∃ value type, store.read? index = some value ∧
      world[index]? = some (Core.OptionalCell.cellType type) ∧
      CellRepresents cell value type := by
  induction related generalizing index with
  | nil => cases selected
  | cons head tail inductionHypothesis =>
      cases selected with
      | head => exact ⟨_, _, rfl, rfl, head⟩
      | tail selected => exact inductionHypothesis selected

theorem HeapRepresents.read {heap : Dynamic.Heap} {store : Core.Store}
    {world : Core.StoreTyping} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (related : HeapRepresents heap.cells store world)
    (read : Dynamic.Heap.Reads heap location cell) :
    ∃ value type, store.read? location.index = some value ∧
      world[location.index]? = some (Core.OptionalCell.cellType type) ∧
      CellRepresents cell value type := by
  cases read with
  | intro selected => exact related.at selected

private theorem stagedRuntimeTyped (value : SourceStagedValue.Value)
    (world : Core.StoreTyping) (definitions : Core.DataEnvironment) :
    Core.RuntimeValueHasType world (SourceStagedValue.toCore value)
      (SourceStagedValue.coreType value) definitions := by
  induction value with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | product _ _ left right => exact .pair left right

theorem CellRepresents.runtime_hasType {cell : Dynamic.Cell} {value : Core.Value}
    {type : Core.Ty} (related : CellRepresents cell value type)
    (world : Core.StoreTyping) (definitions : Core.DataEnvironment) :
    Core.RuntimeValueHasType world value (Core.OptionalCell.cellType type) definitions := by
  cases related with
  | uninitialized _ => exact .inLeft .unit
  | initialized value => exact .inRight (stagedRuntimeTyped value world definitions)

private theorem HeapRepresents.lookup {cells : List Dynamic.Cell} {store : Core.Store}
    {world : Core.StoreTyping} {index : Nat} {type : Core.Ty}
    (related : HeapRepresents cells store world) (found : world[index]? = some type)
    (runtimeWorld : Core.StoreTyping) (definitions : Core.DataEnvironment) :
    ∃ value, store.read? index = some value ∧
      Core.RuntimeValueHasType runtimeWorld value type definitions := by
  induction related generalizing index with
  | nil => simp at found
  | cons head tail inductionHypothesis =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst type
          exact ⟨_, rfl, head.runtime_hasType runtimeWorld definitions⟩
      | succ index => exact inductionHypothesis found

/-- The structural heap relation establishes the actual general Core store
invariant, with the same optional-cell world at every index. -/
theorem HeapRepresents.runtime_hasTypes {cells : List Dynamic.Cell} {store : Core.Store}
    {world : Core.StoreTyping} (related : HeapRepresents cells store world)
    (definitions : Core.DataEnvironment) : Core.RuntimeStoreHasTypes world store definitions where
  length_eq := by
    induction related with
    | nil => rfl
    | cons _ _ inductionHypothesis => simpa using congrArg Nat.succ inductionHypothesis
  lookup := fun found => related.lookup found world definitions

/-- Ordinary source lookup and Core's positional lookup may differ in names;
both refer to the same stable heap index. -/
structure ReadSite (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (payloadType : Core.Ty) where
  node : ExpressionNode
  binder : Resolved.LocalId
  name : String
  index : Nat
  contains : ContainsExpression source id node
  form : node.form = .reference name (.local binder)
  owner : binder.owner = source.owner
  requirements : node.requirements = []
  coercions : node.coercions = []
  slot : SourceCoreLocalCell.lookup? scope binder = some (index, payloadType)
  types : TypeRepresents node.type payloadType

theorem ReadSite.lower {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {payloadType : Core.Ty}
    (site : ReadSite source scope id payloadType) (unique : NodeOccurrencesUnique source)
    (reason : Core.Word) :
    SourceCoreLocalCell.lowerRead source scope id reason =
      .ok (Core.OptionalCell.read payloadType (.var site.index) reason) :=
  SourceCoreLocalCell.lowerRead_eq (lookupExpression?_complete unique site.contains)
    site.form site.owner site.requirements site.coercions site.slot
    (site.types.lower _) reason

theorem ReadSite.core_hasType {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {payloadType : Core.Ty}
    (site : ReadSite source scope id payloadType) (reason : Core.Word)
    (definitions : Core.DataEnvironment) :
    Core.HasType (SourceCoreLocalCell.coreContext scope)
      (Core.OptionalCell.read payloadType (.var site.index) reason)
      (Core.LanguageResult.resultType payloadType) definitions := by
  exact Core.OptionalCell.read_hasType reason (site.types.wellFormed definitions)
    (.var (SourceCoreLocalCell.lookup?_context site.slot))

/-- A source uninitialized read produces the encoded failure and preserves
both heaps. The supplied reason word identifies this source fault site. -/
theorem ReadSite.uninitialized {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {payloadType : Core.Ty}
    (site : ReadSite source scope id payloadType)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (coreEnvironment : Core.Environment) (store : Core.Store)
    (location : Dynamic.Location) (cell : Dynamic.Cell)
    (lookup : Dynamic.Environment.LooksUp environment site.binder location)
    (read : Dynamic.Heap.Reads heap location cell)
    (cellType : cell.type = site.node.type) (descriptor : cell.generalized = none)
    (empty : cell.value = none)
    (coreLookup : coreEnvironment[site.index]? =
      some (.cellRef (Core.OptionalCell.cellType payloadType) location.index))
    (coreRead : store.read? location.index = some (.inLeft payloadType .unit))
    (reason : Core.Word) :
    Dynamic.ExpressionFaults program context evidence source environment heap id
      (.uninitializedLocation location) heap ∧
    Core.Evaluates coreEnvironment store
      (Core.OptionalCell.read payloadType (.var site.index) reason)
      (.inLeft payloadType (.word reason)) store := by
  constructor
  · apply Dynamic.ExpressionFaults.form site.contains
    rw [site.form, site.requirements, site.coercions]
    exact .localUninitialized (owned := []) rfl lookup read descriptor empty
      (cellType ▸ site.types.not_mapping)
  · exact Core.OptionalCell.read_failure reason (.var coreLookup) coreRead

theorem ReadSite.initialized {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {payloadType : Core.Ty}
    (site : ReadSite source scope id payloadType)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (coreEnvironment : Core.Environment) (store : Core.Store)
    (location : Dynamic.Location) (cell : Dynamic.Cell)
    (value : SourceStagedValue.Value)
    (lookup : Dynamic.Environment.LooksUp environment site.binder location)
    (read : Dynamic.Heap.Reads heap location cell) (descriptor : cell.generalized = none)
    (initialized : cell.value = some (StagedValue.toSource value))
    (coreLookup : coreEnvironment[site.index]? =
      some (.cellRef (Core.OptionalCell.cellType payloadType) location.index))
    (coreRead : store.read? location.index =
      some (.inRight .unit (SourceStagedValue.toCore value)))
    (reason : Core.Word) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id
      (StagedValue.toSource value) heap ∧
    Core.Evaluates coreEnvironment store
      (Core.OptionalCell.read payloadType (.var site.index) reason)
      (.inRight .word (SourceStagedValue.toCore value)) store := by
  constructor
  · apply Dynamic.ExpressionEvaluates.intro site.contains
    · rw [site.form, site.requirements, site.coercions]
      exact .local rfl lookup read descriptor initialized
    · rw [site.coercions]
      exact .nil
  · exact Core.OptionalCell.read_success reason (.var coreLookup) coreRead

/-- A compiler reason identifies this read site's uninitialized source fault.
Success retains the established scalar/product representation. -/
inductive OutcomeRepresents (location : Dynamic.Location) (reason : Core.Word) :
    Dynamic.ExpressionOutcome → Core.Value → Prop where
  | initialized (value : SourceStagedValue.Value) :
      OutcomeRepresents location reason (.value (StagedValue.toSource value))
        (.inRight .word (SourceStagedValue.toCore value))
  | uninitialized (type : Core.Ty) :
      OutcomeRepresents location reason (.fault (.uninitializedLocation location))
        (.inLeft type (.word reason))

/-- Heap correspondence determines the Core load, including the absent case;
the caller supplies only lexical resolution to the same heap location. -/
theorem ReadSite.preserves {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {payloadType : Core.Ty}
    (site : ReadSite source scope id payloadType)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (coreEnvironment : Core.Environment) (store : Core.Store) (world : Core.StoreTyping)
    (location : Dynamic.Location) (cell : Dynamic.Cell)
    (related : HeapRepresents heap.cells store world)
    (lookup : Dynamic.Environment.LooksUp environment site.binder location)
    (read : Dynamic.Heap.Reads heap location cell) (cellType : cell.type = site.node.type)
    (coreLookup : coreEnvironment[site.index]? =
      some (.cellRef (Core.OptionalCell.cellType payloadType) location.index))
    (reason : Core.Word) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
        sourceOutcome heap ∧
      OutcomeRepresents location reason sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store
        (Core.OptionalCell.read payloadType (.var site.index) reason) coreValue store := by
  obtain ⟨stored, type, coreRead, _, represents⟩ := related.read read
  have projected := represents.types.lower (.occurrence id.occurrence)
  rw [cellType] at projected
  have same : type = payloadType := Except.ok.inj (projected.symm.trans (site.types.lower _))
  subst type
  cases represents with
  | uninitialized types =>
      obtain ⟨sourceFault, coreEvaluation⟩ := site.uninitialized program context evidence
        environment heap coreEnvironment store location _ lookup read cellType rfl rfl
        coreLookup coreRead reason
      exact ⟨_, _, .fault sourceFault, .uninitialized _, coreEvaluation⟩
  | initialized value =>
      obtain ⟨sourceEvaluation, coreEvaluation⟩ := site.initialized program context evidence
        environment heap coreEnvironment store location _ value lookup read rfl rfl
        coreLookup coreRead reason
      exact ⟨_, _, .value sourceEvaluation, .initialized value, coreEvaluation⟩

/-- The actual local-read compiler has a finite execution corresponding to the
independent source outcome. Every completed Core run has that same value and
unchanged store. No source-evaluator execution is a premise. -/
theorem ReadSite.lower_run_preserves {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {payloadType : Core.Ty}
    (site : ReadSite source scope id payloadType) (unique : NodeOccurrencesUnique source)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (coreEnvironment : Core.Environment) (store : Core.Store) (world : Core.StoreTyping)
    (location : Dynamic.Location) (cell : Dynamic.Cell)
    (related : HeapRepresents heap.cells store world)
    (lookup : Dynamic.Environment.LooksUp environment site.binder location)
    (read : Dynamic.Heap.Reads heap location cell) (cellType : cell.type = site.node.type)
    (coreLookup : coreEnvironment[site.index]? =
      some (.cellRef (Core.OptionalCell.cellType payloadType) location.index))
    (reason : Core.Word) :
    ∃ expression sourceOutcome coreValue required,
      SourceCoreLocalCell.lowerRead source scope id reason = .ok expression ∧
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
        sourceOutcome heap ∧
      OutcomeRepresents location reason sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel
        (.initial expression coreEnvironment store) = .done coreValue store) ∧
      (∀ fuel result finalStore, Core.runStateful fuel
        (.initial expression coreEnvironment store) = .done result finalStore →
          result = coreValue ∧ finalStore = store) := by
  obtain ⟨sourceOutcome, coreValue, sourceEvaluation, outcome, coreEvaluation⟩ :=
    site.preserves program context evidence environment heap coreEnvironment store world
      location cell related lookup read cellType coreLookup reason
  obtain ⟨required, completes⟩ :=
    Core.evaluation_runStateful_complete_with_sufficient_fuel coreEvaluation
  refine ⟨_, sourceOutcome, coreValue, required, site.lower unique reason,
    sourceEvaluation, outcome, completes, ?_⟩
  intro fuel result finalStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed)
    coreEvaluation

end Solcore.SourceSemantics.CoreLowering.LocalCell
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.HeapMutation
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralHeap
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralHeapFrame
/-! Source execution preserves existing administrative cells: they remain
outside the source map and retain their exact Core values. This is stronger
than the general runtime typing of the final store and keeps installed global
code available to later calls. Newly allocated cells are outside this frame. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.GeneralHeap

/-- Existing Core locations without a source alias keep their contents and
cannot become source aliases during this execution. -/
def AdministrativePreserved (mapping : LocationMap) (store : Core.Store)
    (futureMapping : LocationMap) (futureStore : Core.Store) : Prop :=
  ∀ location, location ∉ mapping → location < store.length →
    location ∉ futureMapping ∧ futureStore.read? location = store.read? location

namespace AdministrativePreserved

theorem refl (mapping : LocationMap) (store : Core.Store) : AdministrativePreserved mapping store mapping store := by
  intro location absent _
  exact ⟨absent, rfl⟩

theorem trans {firstMap secondMap thirdMap : LocationMap} {first second third : Core.Store}
    (left : AdministrativePreserved firstMap first secondMap second)
    (right : AdministrativePreserved secondMap second thirdMap third) :
    AdministrativePreserved firstMap first thirdMap third := by
  intro location absent bound
  obtain ⟨middleAbsent, same⟩ := left location absent bound
  have firstRead : first.read? location = some first[location] := List.getElem?_eq_getElem bound
  have middleBound : location < second.length :=
    (List.getElem?_eq_some_iff.mp (same.trans firstRead)).1
  obtain ⟨lastAbsent, lastSame⟩ := right location middleAbsent middleBound
  exact ⟨lastAbsent, lastSame.trans same⟩

theorem allocate (mapping : LocationMap) (store : Core.Store) (value : Core.Value) :
    AdministrativePreserved mapping store (mapping ++ [store.length]) (store.allocate value).1 := by
  intro location absent bound
  refine ⟨?_, Core.Store.allocate_old_lookup store value bound⟩
  simp only [List.mem_append, List.mem_singleton, not_or]
  exact ⟨absent, Nat.ne_of_lt bound⟩

theorem allocate_administrative (mapping : LocationMap) (store : Core.Store) (value : Core.Value) :
    AdministrativePreserved mapping store mapping (store.allocate value).1 := by
  intro location absent bound
  exact ⟨absent, Core.Store.allocate_old_lookup store value bound⟩

theorem write {mapping : LocationMap} {store updated : Core.Store}
    {location : Core.Location} {value : Core.Value}
    (mapped : location ∈ mapping) (written : store.write? location value = some updated) :
    AdministrativePreserved mapping store mapping updated := by
  intro other absent _
  have different : other ≠ location := by intro same; exact absent (same ▸ mapped)
  exact ⟨absent, Core.Store.write?_preserves_other written different⟩

end AdministrativePreserved

end Solcore.SourceSemantics.CoreLowering.GeneralHeap
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.OrderedMapping
/-! Generic library correspondence to independent source ordered mappings.
Key/value representation and the generated comparator's correctness are explicit
boundaries; this is not a certificate for a complete source compiler. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.OrderedMapping

open Core.OrderedMapping

abbrev Relation := Dynamic.Value → Core.Value → Prop

inductive EntriesRel (keyRel valueRel : Relation) :
    List (Dynamic.Value × Dynamic.Value) → Entries → Prop where
  | nil : EntriesRel keyRel valueRel [] []
  | cons {sourceKey sourceValue : Dynamic.Value} {key value : Core.Value}
      {sourceRest : List (Dynamic.Value × Dynamic.Value)} {rest : Entries}
      (keyRelated : keyRel sourceKey key) (valueRelated : valueRel sourceValue value)
      (tail : EntriesRel keyRel valueRel sourceRest rest) :
      EntriesRel keyRel valueRel ((sourceKey, sourceValue) :: sourceRest) ((key, value) :: rest)

def ValueRel (layout : Layout) (keyRel valueRel : Relation)
    (entries : List (Dynamic.Value × Dynamic.Value)) (carrier : Core.Value) : Prop :=
  ∃ coreEntries, EntriesRel keyRel valueRel entries coreEntries ∧ carrier = encode layout coreEntries

/-- Equality may be non-reflexive, for example for ordinary source closures.
No generic equality of functions or mappings is assumed. -/
structure KeyEqualityCorrect (keyRel : Relation) (equal : Predicate) : Prop where
  equivalent : ∀ {sourceKey sourceStored : Dynamic.Value} {key stored : Core.Value},
    keyRel sourceKey key → keyRel sourceStored stored →
      (equal key stored = true ↔ Dynamic.ValueEquivalent sourceKey sourceStored)

theorem EntriesRel.append {keyRel valueRel : Relation}
    {sourceLeft sourceRight : List (Dynamic.Value × Dynamic.Value)} {left right : Entries}
    (leftRelated : EntriesRel keyRel valueRel sourceLeft left)
    (rightRelated : EntriesRel keyRel valueRel sourceRight right) :
    EntriesRel keyRel valueRel (sourceLeft ++ sourceRight) (left ++ right) := by
  induction leftRelated with
  | nil => exact rightRelated
  | cons key value _ ih => exact .cons key value ih

theorem lookup_related {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal)
    {sourceKey sourceResult : Dynamic.Value} {key : Core.Value}
    {sourceEntries : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (related : EntriesRel keyRel valueRel sourceEntries entries)
    (found : Dynamic.MappingLookup sourceKey sourceEntries sourceResult) :
    ∃ value, lookupEntries equal key entries = some value ∧ valueRel sourceResult value := by
  induction related with
  | nil => cases found
  | @cons sourceStored sourceValue stored value sourceRest rest storedRelated valueRelated tail ih =>
      cases found with
      | head equivalent =>
          have same := (correct.equivalent keyRelated storedRelated).mpr equivalent
          exact ⟨value, by simp [lookupEntries, same], valueRelated⟩
      | tail different found =>
          have unequal : equal key stored = false := Bool.eq_false_iff.mpr
            (fun same => different ((correct.equivalent keyRelated storedRelated).mp same))
          obtain ⟨result, lookup, relation⟩ := ih found
          exact ⟨result, by simpa [lookupEntries, unequal] using lookup, relation⟩

theorem absent_related {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal)
    {sourceKey : Dynamic.Value} {key : Core.Value}
    {sourceEntries : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (related : EntriesRel keyRel valueRel sourceEntries entries)
    (absent : Dynamic.MappingAbsent sourceKey sourceEntries) :
    lookupEntries equal key entries = none := by
  induction related with
  | nil => rfl
  | @cons sourceStored sourceValue stored value sourceRest rest storedRelated valueRelated tail ih =>
      cases absent with
      | cons different absent =>
          have unequal : equal key stored = false := Bool.eq_false_iff.mpr
            (fun same => different ((correct.equivalent keyRelated storedRelated).mp same))
          simpa [lookupEntries, unequal] using ih absent

private theorem update_related {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal)
    {sourceKey sourceValue : Dynamic.Value} {key value : Core.Value}
    {sourceEntries updated : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (valueRelated : valueRel sourceValue value)
    (related : EntriesRel keyRel valueRel sourceEntries entries)
    (updatedSource : Dynamic.MappingUpdate sourceKey sourceValue sourceEntries updated) :
    EntriesRel keyRel valueRel updated (insertEntries equal key value entries) := by
  induction related generalizing updated with
  | nil => cases updatedSource
  | @cons sourceStored sourceOld stored old sourceRest rest storedRelated oldRelated tail ih =>
      cases updatedSource with
      | head equivalent =>
          have same := (correct.equivalent keyRelated storedRelated).mpr equivalent
          simp only [insertEntries, same, ↓reduceIte]
          exact .cons keyRelated valueRelated tail
      | tail different updatedSource =>
          have unequal : equal key stored = false := Bool.eq_false_iff.mpr
            (fun same => different ((correct.equivalent keyRelated storedRelated).mp same))
          simp only [insertEntries, unequal, Bool.false_eq_true, ↓reduceIte]
          exact .cons storedRelated oldRelated (ih updatedSource)

private theorem insert_absent {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal)
    {sourceKey : Dynamic.Value} {key value : Core.Value}
    {sourceEntries : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (related : EntriesRel keyRel valueRel sourceEntries entries)
    (absent : Dynamic.MappingAbsent sourceKey sourceEntries) :
    insertEntries equal key value entries = entries ++ [(key, value)] := by
  induction related with
  | nil => rfl
  | @cons sourceStored sourceOld stored old sourceRest rest storedRelated oldRelated tail ih =>
      cases absent with
      | cons different absent =>
          have unequal : equal key stored = false := Bool.eq_false_iff.mpr
            (fun same => different ((correct.equivalent keyRelated storedRelated).mp same))
          simp [insertEntries, unequal, ih absent]

theorem insert_related {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal)
    {sourceKey sourceValue : Dynamic.Value} {key value : Core.Value}
    {sourceEntries updated : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (valueRelated : valueRel sourceValue value)
    (related : EntriesRel keyRel valueRel sourceEntries entries)
    (inserted : Dynamic.MappingInsert sourceKey sourceValue sourceEntries updated) :
    EntriesRel keyRel valueRel updated (insertEntries equal key value entries) := by
  cases inserted with
  | update replacement => exact update_related correct keyRelated valueRelated related replacement
  | append absent =>
      rw [insert_absent correct keyRelated related absent]
      exact related.append (.cons keyRelated valueRelated .nil)

/-- A related source insertion and actual pure comparator executions entail a
finite Core run with a related carrier. Administrative cells remain explicit. -/
theorem insert_run_preserves {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal) (layout : Layout)
    {sourceKey sourceValue : Dynamic.Value} {key value comparator : Core.Value}
    {sourceEntries updated : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (valueRelated : valueRel sourceValue value)
    (related : EntriesRel keyRel valueRel sourceEntries entries)
    (inserted : Dynamic.MappingInsert sourceKey sourceValue sourceEntries updated)
    {environment : Core.Environment} {initialStore mappingStore keyStore valueStore comparisonStore : Core.Store}
    {mapping keyExpr valueExpr keyEqual : Core.Expr}
    (mappingEvaluated : Core.Evaluates environment initialStore mapping (encode layout entries) mappingStore)
    (keyEvaluated : Core.Evaluates environment mappingStore keyExpr key keyStore)
    (valueEvaluated : Core.Evaluates environment keyStore valueExpr value valueStore)
    (comparatorEvaluated : Core.Evaluates environment valueStore keyEqual comparator comparisonStore)
    (comparisons : Comparisons layout comparator equal key entries
      (installedStore comparisonStore layout.insertParameter layout.type (insertBody layout)
        (.pair (encode layout entries) (.pair (.pair key value) comparator)) environment)) :
    ∃ output finalStore required, ValueRel layout keyRel valueRel updated output ∧
      ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (Core.State.initial (insert layout keyEqual mapping keyExpr valueExpr) environment initialStore) =
          .done (.inRight .word output) finalStore := by
  have evaluation := insert_evaluates entries key value comparator equal
    mappingEvaluated keyEvaluated valueEvaluated comparatorEvaluated comparisons
  obtain ⟨required, complete⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluation
  exact ⟨_, _, required, ⟨_, insert_related correct keyRelated valueRelated related inserted, rfl⟩, complete⟩

theorem lookup_found_run_preserves {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal) (layout : Layout)
    {sourceKey sourceResult : Dynamic.Value} {key comparator : Core.Value}
    {sourceEntries : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (related : EntriesRel keyRel valueRel sourceEntries entries)
    (found : Dynamic.MappingLookup sourceKey sourceEntries sourceResult)
    {environment : Core.Environment} {initialStore mappingStore keyStore comparisonStore : Core.Store}
    {mapping keyExpr keyEqual : Core.Expr}
    (mappingEvaluated : Core.Evaluates environment initialStore mapping (encode layout entries) mappingStore)
    (keyEvaluated : Core.Evaluates environment mappingStore keyExpr key keyStore)
    (comparatorEvaluated : Core.Evaluates environment keyStore keyEqual comparator comparisonStore)
    (comparisons : Comparisons layout comparator equal key entries
      (installedStore comparisonStore layout.lookupParameter layout.lookupResult (lookupBody layout)
        (.pair (encode layout entries) (.pair key comparator)) environment)) :
    ∃ output finalStore required, valueRel sourceResult output ∧
      ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (Core.State.initial (lookup layout keyEqual mapping keyExpr) environment initialStore) =
          .done (.inRight .word (.inRight .unit output)) finalStore := by
  obtain ⟨output, located, represented⟩ := lookup_related correct keyRelated related found
  have evaluation := lookup_evaluates entries key comparator equal
    mappingEvaluated keyEvaluated comparatorEvaluated comparisons
  rw [located] at evaluation
  obtain ⟨required, complete⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluation
  exact ⟨output, _, required, represented, complete⟩

theorem lookup_absent_run_preserves {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal) (layout : Layout)
    {sourceKey : Dynamic.Value} {key comparator : Core.Value}
    {sourceEntries : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (related : EntriesRel keyRel valueRel sourceEntries entries)
    (absent : Dynamic.MappingAbsent sourceKey sourceEntries)
    {environment : Core.Environment} {initialStore mappingStore keyStore comparisonStore : Core.Store}
    {mapping keyExpr keyEqual : Core.Expr}
    (mappingEvaluated : Core.Evaluates environment initialStore mapping (encode layout entries) mappingStore)
    (keyEvaluated : Core.Evaluates environment mappingStore keyExpr key keyStore)
    (comparatorEvaluated : Core.Evaluates environment keyStore keyEqual comparator comparisonStore)
    (comparisons : Comparisons layout comparator equal key entries
      (installedStore comparisonStore layout.lookupParameter layout.lookupResult (lookupBody layout)
        (.pair (encode layout entries) (.pair key comparator)) environment)) :
    ∃ finalStore required, ∀ fuel, required ≤ fuel →
      Core.runStateful fuel (Core.State.initial (lookup layout keyEqual mapping keyExpr) environment initialStore) =
        .done (.inRight .word (.inLeft layout.valueType .unit)) finalStore := by
  have evaluation := lookup_evaluates entries key comparator equal
    mappingEvaluated keyEvaluated comparatorEvaluated comparisons
  rw [absent_related correct keyRelated related absent] at evaluation
  obtain ⟨required, complete⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluation
  exact ⟨_, required, complete⟩

/-- Source insertion is related to the actual post-RHS root write; earlier root
contents are unrestricted. Comparator setup also precedes the final root read. -/
theorem assign_latest_preserves {keyRel valueRel : Relation} {equal : Predicate}
    (correct : KeyEqualityCorrect keyRel equal) (layout : Layout)
    {sourceKey sourceValue : Dynamic.Value} {key value comparator : Core.Value}
    {sourceEntries updated : List (Dynamic.Value × Dynamic.Value)} {entries : Entries}
    (keyRelated : keyRel sourceKey key) (valueRelated : valueRel sourceValue value)
    (related : EntriesRel keyRel valueRel sourceEntries entries)
    (inserted : Dynamic.MappingInsert sourceKey sourceValue sourceEntries updated)
    {environment : Core.Environment} {initialStore referenceStore keyStore rhsStore comparisonStore : Core.Store}
    {keyEqual reference keyExpr rhs : Core.Expr} {location : Core.Location}
    (referenceEvaluated : Core.Evaluates environment initialStore reference
      (.cellRef (Core.OptionalCell.cellType layout.type) location) referenceStore)
    (keyEvaluated : Core.Evaluates (.cellRef (Core.OptionalCell.cellType layout.type) location :: environment)
      referenceStore (keyExpr.weakenAt 0) (.inRight .word key) keyStore)
    (rhsEvaluated : Core.Evaluates (key :: .cellRef (Core.OptionalCell.cellType layout.type) location :: environment)
      keyStore ((rhs.weakenAt 0).weakenAt 0) (.inRight .word value) rhsStore)
    (comparisonEvaluated : Core.Evaluates
      (value :: key :: .cellRef (Core.OptionalCell.cellType layout.type) location :: environment)
      rhsStore (((keyEqual.weakenAt 0).weakenAt 0).weakenAt 0) comparator comparisonStore)
    (latest : comparisonStore.read? location = some (.inRight .unit (encode layout entries)))
    (comparisons : Comparisons layout comparator equal key entries
      (assignInsertStore layout comparisonStore entries key value comparator location environment)) :
    ∃ output finalStore, ValueRel layout keyRel valueRel updated output ∧
      finalStore.read? location = some (.inRight .unit output) ∧
      Core.Evaluates environment initialStore (assign layout keyEqual reference keyExpr rhs)
        (.inRight .word .unit) finalStore := by
  refine ⟨_, _, ⟨_, insert_related correct keyRelated valueRelated related inserted, rfl⟩, ?_,
    assign_latest_evaluates entries key value comparator equal
      referenceEvaluated keyEvaluated rhsEvaluated comparisonEvaluated latest comparisons⟩
  have inBounds : location < comparisonStore.length := (List.getElem?_eq_some_iff.mp latest).choose
  have allocatedBounds : location <
      (assignInsertStore layout comparisonStore entries key value comparator location environment).length := by
    simpa [assignInsertStore, installedStore, Core.WordMapping.installedStore] using Nat.lt_succ_of_lt inBounds
  simp [Core.Store.read?, allocatedBounds]

end Solcore.SourceSemantics.CoreLowering.OrderedMapping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AmbientDefinitions
/-! A source catalog keeps its own nominal identities. Additional ordinary Core
definitions are an authenticated suffix, not invented source declarations.
This receipt transports old registrations and typing without claiming that new
administrative closures were typable in the smaller catalog. -/
set_option autoImplicit false
namespace Solcore.Core

structure AmbientDefinitions (base : DataEnvironment) where
  definitions : DataEnvironment
  basePrefix : base.Extends definitions

def AmbientDefinitions.original (base : DataEnvironment) : AmbientDefinitions base :=
  ⟨base, .refl base⟩

def AmbientDefinitions.append (base suffix : DataEnvironment) : AmbientDefinitions base :=
  ⟨base ++ suffix, .append base suffix⟩

theorem OrderedMapping.Layout.Registered.extend_definitions {base future : DataEnvironment}
    {layout : OrderedMapping.Layout} (registered : layout.Registered base)
    (extension : base.Extends future) : layout.Registered future :=
  ⟨registered.keyWellFormed.extend_definitions extension,
    registered.valueWellFormed.extend_definitions extension, extension.lookup registered.lookup⟩

end Solcore.Core
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.HeapEffectsRenaming
/-! Exact binder insertion for Core expressions that may allocate, load, and
write existing values, but do not create or call closures. Mutation preserves
the original value and store under renaming because no capture environment is
rebuilt. Administrative closure cells are allowed in the initial store. -/

set_option autoImplicit false

namespace Solcore.Core.HeapEffects

inductive Expression : Expr → Prop where
  | unit : Expression .unit
  | bool {value} : Expression (.bool value)
  | word {value} : Expression (.word value)
  | var {index} : Expression (.var index)
  | pair {left right} : Expression left → Expression right → Expression (.pair left right)
  | first {operand} : Expression operand → Expression (.first operand)
  | second {operand} : Expression operand → Expression (.second operand)
  | inLeft {type payload} : Expression payload → Expression (.inLeft type payload)
  | inRight {type payload} : Expression payload → Expression (.inRight type payload)
  | caseE {scrutinee left right} : Expression scrutinee → Expression left → Expression right →
      Expression (.caseE scrutinee left right)
  | newCell {type initializer} : Expression initializer → Expression (.newCell type initializer)
  | storeCell {reference value} : Expression reference → Expression value → Expression (.storeCell reference value)
  | loadCell {reference} : Expression reference → Expression (.loadCell reference)
  | unary {operator operand} : Expression operand → Expression (.unary operator operand)
  | binary {operator left right} : Expression left → Expression right → Expression (.binary operator left right)
  | ternary {operator first second third} : Expression first → Expression second → Expression third →
      Expression (.ternary operator first second third)
  | letE {value body} : Expression value → Expression body → Expression (.letE value body)
  | ifE {condition left right} : Expression condition → Expression left → Expression right →
      Expression (.ifE condition left right)

theorem Expression.of_readOnly {expression : Expr} (restricted : ReadOnly.Expression expression) :
    Expression expression := by
  induction restricted with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | var => exact .var
  | pair _ _ left right => exact .pair left right
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih
  | inLeft _ ih => exact .inLeft ih
  | inRight _ ih => exact .inRight ih
  | caseE _ _ _ scrutinee left right => exact .caseE scrutinee left right
  | loadCell _ ih => exact .loadCell ih
  | unary _ ih => exact .unary ih
  | binary _ _ left right => exact .binary left right
  | ternary _ _ _ first second third => exact .ternary first second third
  | letE _ _ value body => exact .letE value body
  | ifE _ _ _ condition left right => exact .ifE condition left right

theorem Expression.rename {expression : Expr} (restricted : Expression expression) (mapping : Renaming) :
    Expression (expression.rename mapping) := by
  induction restricted generalizing mapping with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | var => exact .var
  | pair _ _ left right => exact .pair (left mapping) (right mapping)
  | first _ ih => exact .first (ih mapping)
  | second _ ih => exact .second (ih mapping)
  | inLeft _ ih => exact .inLeft (ih mapping)
  | inRight _ ih => exact .inRight (ih mapping)
  | caseE _ _ _ scrutinee left right => exact .caseE (scrutinee mapping) (left mapping.lift) (right mapping.lift)
  | newCell _ ih => exact .newCell (ih mapping)
  | storeCell _ _ reference value => exact .storeCell (reference mapping) (value mapping)
  | loadCell _ ih => exact .loadCell (ih mapping)
  | unary _ ih => exact .unary (ih mapping)
  | binary _ _ left right => exact .binary (left mapping) (right mapping)
  | ternary _ _ _ first second third => exact .ternary (first mapping) (second mapping) (third mapping)
  | letE _ _ value body => exact .letE (value mapping) (body mapping.lift)
  | ifE _ _ _ condition left right => exact .ifE (condition mapping) (left mapping) (right mapping)

theorem Expression.weakenAt {expression : Expr} (restricted : Expression expression) (cutoff : Nat) :
    Expression (expression.weakenAt cutoff) := by
  simpa using restricted.rename (Renaming.insertion cutoff)

/-- Transport an existing finite evaluation using the syntax restriction and
lookup agreement. No store typing or first-order payload premise is needed. -/
theorem Expression.evaluation_rename {expression : Expr} (restricted : Expression expression)
    {environment target : Environment} {before after : Store} {result : Value} {mapping : Renaming}
    (evaluation : Evaluates environment before expression result after)
    (related : ReadOnly.EnvironmentsAgree mapping environment target) :
    Evaluates target before (expression.rename mapping) result after := by
  induction restricted generalizing environment target before after result mapping with
  | unit => cases evaluation; exact .unit
  | bool => cases evaluation; exact .bool
  | word => cases evaluation; exact .word
  | var => cases evaluation with | var found => exact .var (related found)
  | pair _ _ left right =>
      cases evaluation with
      | pair leftEvaluation rightEvaluation => exact .pair (left leftEvaluation related) (right rightEvaluation related)
  | first _ ih => cases evaluation with | first evaluated => exact .first (ih evaluated related)
  | second _ ih => cases evaluation with | second evaluated => exact .second (ih evaluated related)
  | inLeft _ ih => cases evaluation with | inLeft evaluated => exact .inLeft (ih evaluated related)
  | inRight _ ih => cases evaluation with | inRight evaluated => exact .inRight (ih evaluated related)
  | caseE _ _ _ scrutinee left right =>
      cases evaluation with
      | caseLeft selected branch => exact .caseLeft (scrutinee selected related) (left branch (related.lift _))
      | caseRight selected branch => exact .caseRight (scrutinee selected related) (right branch (related.lift _))
  | newCell _ ih => cases evaluation with | newCell evaluated => exact .newCell (ih evaluated related)
  | storeCell _ _ reference value =>
      cases evaluation with
      | storeCell referenceEvaluation read valueEvaluation written =>
          exact .storeCell (reference referenceEvaluation related) read (value valueEvaluation related) written
  | loadCell _ ih =>
      cases evaluation with
      | loadCell reference read => exact .loadCell (ih reference related) read
  | unary _ ih => cases evaluation with | unary evaluated applied => exact .unary (ih evaluated related) applied
  | binary _ _ left right =>
      cases evaluation with
      | binary leftEvaluation rightEvaluation applied =>
          exact .binary (left leftEvaluation related) (right rightEvaluation related) applied
  | ternary _ _ _ first second third =>
      cases evaluation with
      | ternary firstEvaluation secondEvaluation thirdEvaluation applied =>
          exact .ternary (first firstEvaluation related) (second secondEvaluation related) (third thirdEvaluation related) applied
  | letE _ _ value body =>
      cases evaluation with
      | letE evaluated branch => exact .letE (value evaluated related) (body branch (related.lift _))
  | ifE _ _ _ condition left right =>
      cases evaluation with
      | ifTrue selected branch => exact .ifTrue (condition selected related) (left branch related)
      | ifFalse selected branch => exact .ifFalse (condition selected related) (right branch related)

theorem Expression.evaluation_weakenAt {expression : Expr} (restricted : Expression expression)
    {environment : Environment} {before after : Store} {result : Value}
    (evaluation : Evaluates environment before expression result after) (cutoff : Nat) (inserted : Value) :
    Evaluates (Environment.insertAt environment cutoff inserted) before (expression.weakenAt cutoff) result after := by
  simpa using restricted.evaluation_rename evaluation (ReadOnly.EnvironmentsAgree.insertion environment cutoff inserted)

theorem Expression.evaluation_weakenAt_zero {expression : Expr} (restricted : Expression expression)
    {environment : Environment} {before after : Store} {result : Value}
    (evaluation : Evaluates environment before expression result after) (inserted : Value) :
    Evaluates (inserted :: environment) before (expression.weakenAt 0) result after := by
  simpa [Environment.insertAt] using restricted.evaluation_weakenAt evaluation 0 inserted

end Solcore.Core.HeapEffects
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.WordMapping
/-! Structural correspondence for the fixed Word/Word mapping prototype.
The source side is the independent declarative ordered-mapping semantics.
There is no call to the executable typed-source runtime. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.WordMapping

open Core

def sourceEntries : Core.WordMapping.Entries → List (Dynamic.Value × Dynamic.Value)
  | [] => []
  | (key, value) :: rest => (.word key, .word value) :: sourceEntries rest

/-- Ordered entries are represented structurally, including duplicate keys. -/
inductive ValueRel : List (Dynamic.Value × Dynamic.Value) → Core.Value → Prop where
  | nil : ValueRel [] (.constructed Core.WordMapping.nilConstructor .unit)
  | cons {entries : List (Dynamic.Value × Dynamic.Value)} {tail : Core.Value}
      (key value : Word) (rest : ValueRel entries tail) :
      ValueRel ((.word key, .word value) :: entries)
        (.constructed Core.WordMapping.consConstructor (.pair (.pair (.word key) (.word value)) tail))

/-- The whole source value retains its declared key and value types. -/
def MappingValueRel (source : Dynamic.Value) (target : Core.Value) : Prop :=
  ∃ entries, source = .mapping .word .word entries ∧ ValueRel entries target

theorem ValueRel.encode (entries : Core.WordMapping.Entries) :
    ValueRel (sourceEntries entries) (Core.WordMapping.encode entries) := by
  induction entries with
  | nil => exact .nil
  | cons entry rest ih => exact .cons entry.1 entry.2 ih

theorem ValueRel.canonical {entries : List (Dynamic.Value × Dynamic.Value)} {value : Core.Value}
    (related : ValueRel entries value) :
    ∃ words : Core.WordMapping.Entries, entries = sourceEntries words ∧ value = Core.WordMapping.encode words := by
  induction related with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons key value rest ih =>
      obtain ⟨words, rfl, rfl⟩ := ih
      exact ⟨(key, value) :: words, rfl, rfl⟩

theorem ValueRel.hasType {entries : List (Dynamic.Value × Dynamic.Value)} {value : Core.Value}
    (related : ValueRel entries value) (world : StoreTyping) :
    RuntimeValueHasType world value Core.WordMapping.type Core.WordMapping.actualDefinitions := by
  obtain ⟨words, _, rfl⟩ := related.canonical
  exact Core.WordMapping.encode_hasType words world

private theorem word_equivalent (left right : Word) :
    Dynamic.ValueEquivalent (.word left) (.word right) ↔ left = right := by
  constructor
  · intro same
    exact Dynamic.Value.word.inj same.1
  · rintro rfl
    exact ⟨rfl, .word _⟩

theorem lookupEntries_of_lookup (words : Core.WordMapping.Entries) (key : Word)
    {result : Dynamic.Value}
    (lookup : Dynamic.MappingLookup (.word key) (sourceEntries words) result) :
    result = .word (Core.WordMapping.lookupEntries key words) := by
  induction words with
  | nil => cases lookup
  | cons entry rest ih =>
      rcases entry with ⟨storedKey, value⟩
      cases lookup with
      | head equivalent =>
          have same := (word_equivalent key storedKey).mp equivalent
          simp [Core.WordMapping.lookupEntries, same]
      | tail different lookup =>
          have distinct : key ≠ storedKey := fun same => different ((word_equivalent _ _).mpr same)
          simpa [Core.WordMapping.lookupEntries, distinct] using ih lookup

theorem lookupEntries_of_absent (words : Core.WordMapping.Entries) (key : Word)
    (absent : Dynamic.MappingAbsent (.word key) (sourceEntries words)) :
    Core.WordMapping.lookupEntries key words = Word.zero := by
  induction words with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨storedKey, value⟩
      cases absent with
      | cons different absent =>
          have distinct : key ≠ storedKey := fun same => different ((word_equivalent _ _).mpr same)
          simpa [Core.WordMapping.lookupEntries, distinct] using ih absent

private theorem insert_tail {key value storedKey storedValue : Dynamic.Value}
    {entries updated : List (Dynamic.Value × Dynamic.Value)}
    (different : ¬ Dynamic.ValueEquivalent key storedKey)
    (inserted : Dynamic.MappingInsert key value entries updated) :
    Dynamic.MappingInsert key value ((storedKey, storedValue) :: entries)
      ((storedKey, storedValue) :: updated) := by
  cases inserted with
  | update replacement => exact .update (.tail different replacement)
  | append absent => exact .append (.cons different absent)

/-- The Core specification is accepted by the independent first-update or
append-at-end source relation. No uniqueness assumption on keys is needed. -/
theorem insertEntries_source (words : Core.WordMapping.Entries) (key value : Word) :
    Dynamic.MappingInsert (.word key) (.word value) (sourceEntries words)
      (sourceEntries (Core.WordMapping.insertEntries key value words)) := by
  induction words with
  | nil => exact .append .nil
  | cons entry rest ih =>
      rcases entry with ⟨storedKey, storedValue⟩
      by_cases same : key = storedKey
      · simpa [Core.WordMapping.insertEntries, same, sourceEntries] using
          (Dynamic.MappingInsert.update
            (Dynamic.MappingUpdate.head (entries := sourceEntries rest)
              (storedValue := Dynamic.Value.word storedValue)
              ((word_equivalent key storedKey).mpr same)))
      · have different : ¬ Dynamic.ValueEquivalent (.word key) (.word storedKey) :=
          fun equivalent => same ((word_equivalent _ _).mp equivalent)
        simp only [Core.WordMapping.insertEntries, beq_eq_false_iff_ne.mpr same, Bool.false_eq_true,
          ↓reduceIte, sourceEntries]
        exact insert_tail different ih

/-- Any source insertion has exactly the ordered carrier computed by Core. -/
theorem insertEntries_of_insert (words : Core.WordMapping.Entries) (key value : Word)
    {updated : List (Dynamic.Value × Dynamic.Value)}
    (inserted : Dynamic.MappingInsert (.word key) (.word value) (sourceEntries words) updated) :
    updated = sourceEntries (Core.WordMapping.insertEntries key value words) :=
  Dynamic.MappingInsert.functional inserted (insertEntries_source words key value)

theorem lookup_present_preserves
    {environment : Core.Environment} {initialStore mappingStore keyStore : Core.Store}
    {mapping keyExpr : Core.Expr} {entries : List (Dynamic.Value × Dynamic.Value)}
    {carrier : Core.Value} {key result : Word}
    (related : ValueRel entries carrier)
    (lookup : Dynamic.MappingLookup (.word key) entries (.word result))
    (mappingEvaluated : Evaluates environment initialStore mapping carrier mappingStore)
    (keyEvaluated : Evaluates environment mappingStore keyExpr (.word key) keyStore) :
    ∃ finalStore,
      Evaluates environment initialStore (Core.WordMapping.lookup mapping keyExpr)
        (.inRight .word (.word result)) finalStore := by
  obtain ⟨words, rfl, rfl⟩ := related.canonical
  have same : result = Core.WordMapping.lookupEntries key words :=
    Dynamic.Value.word.inj (lookupEntries_of_lookup words key lookup)
  subst result
  exact ⟨_, Core.WordMapping.lookup_evaluates words key mappingEvaluated keyEvaluated⟩

theorem lookup_absent_preserves
    {environment : Core.Environment} {initialStore mappingStore keyStore : Core.Store}
    {mapping keyExpr : Core.Expr} {entries : List (Dynamic.Value × Dynamic.Value)}
    {carrier : Core.Value} {key : Word}
    (related : ValueRel entries carrier)
    (absent : Dynamic.MappingAbsent (.word key) entries)
    (mappingEvaluated : Evaluates environment initialStore mapping carrier mappingStore)
    (keyEvaluated : Evaluates environment mappingStore keyExpr (.word key) keyStore) :
    ∃ finalStore,
      Evaluates environment initialStore (Core.WordMapping.lookup mapping keyExpr)
        (.inRight .word (.word Word.zero)) finalStore := by
  obtain ⟨words, rfl, rfl⟩ := related.canonical
  obtain evaluated := Core.WordMapping.lookup_evaluates words key mappingEvaluated keyEvaluated
  rw [lookupEntries_of_absent words key absent] at evaluated
  exact ⟨_, evaluated⟩

theorem insert_preserves
    {environment : Core.Environment} {initialStore mappingStore keyStore valueStore : Core.Store}
    {mapping keyExpr valueExpr : Core.Expr}
    {entries updated : List (Dynamic.Value × Dynamic.Value)}
    {carrier : Core.Value} {key value : Word}
    (related : ValueRel entries carrier)
    (inserted : Dynamic.MappingInsert (.word key) (.word value) entries updated)
    (mappingEvaluated : Evaluates environment initialStore mapping carrier mappingStore)
    (keyEvaluated : Evaluates environment mappingStore keyExpr (.word key) keyStore)
    (valueEvaluated : Evaluates environment keyStore valueExpr (.word value) valueStore) :
    ∃ output finalStore, ValueRel updated output ∧
      Evaluates environment initialStore (Core.WordMapping.insert mapping keyExpr valueExpr)
        (.inRight .word output) finalStore := by
  obtain ⟨words, rfl, rfl⟩ := related.canonical
  rw [insertEntries_of_insert words key value inserted]
  exact ⟨_, _, ValueRel.encode _, Core.WordMapping.insert_evaluates words key value
    mappingEvaluated keyEvaluated valueEvaluated⟩

/-- Independent source insertion entails a finite Core runner observation. -/
theorem insert_run_preserves
    {environment : Core.Environment} {initialStore mappingStore keyStore valueStore : Core.Store}
    {mapping keyExpr valueExpr : Core.Expr}
    {entries updated : List (Dynamic.Value × Dynamic.Value)}
    {carrier : Core.Value} {key value : Word}
    (related : ValueRel entries carrier)
    (inserted : Dynamic.MappingInsert (.word key) (.word value) entries updated)
    (mappingEvaluated : Evaluates environment initialStore mapping carrier mappingStore)
    (keyEvaluated : Evaluates environment mappingStore keyExpr (.word key) keyStore)
    (valueEvaluated : Evaluates environment keyStore valueExpr (.word value) valueStore) :
    ∃ output finalStore required, ValueRel updated output ∧
      ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial (Core.WordMapping.insert mapping keyExpr valueExpr) environment initialStore) =
          .done (.inRight .word output) finalStore := by
  obtain ⟨output, finalStore, related, evaluated⟩ := insert_preserves related inserted
    mappingEvaluated keyEvaluated valueEvaluated
  obtain ⟨required, complete⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨output, finalStore, required, related, complete⟩

/-- A source update of the root *after RHS effects* is preserved by the actual
Core writeback helper, and its resulting root contains the related carrier. -/
theorem assign_latest_preserves
    {environment : Core.Environment}
    {initialStore referenceStore keyStore rhsStore : Core.Store}
    {reference keyExpr rhs : Core.Expr} {location : Core.Location}
    {entries updated : List (Dynamic.Value × Dynamic.Value)}
    {carrier : Core.Value} {key value : Word}
    (related : ValueRel entries carrier)
    (inserted : Dynamic.MappingInsert (.word key) (.word value) entries updated)
    (referenceEvaluated : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType Core.WordMapping.type) location) referenceStore)
    (keyEvaluated : Evaluates
      (.cellRef (OptionalCell.cellType Core.WordMapping.type) location :: environment)
      referenceStore (keyExpr.weakenAt 0) (.inRight .word (.word key)) keyStore)
    (rhsEvaluated : Evaluates
      (.word key :: .cellRef (OptionalCell.cellType Core.WordMapping.type) location :: environment)
      keyStore ((rhs.weakenAt 0).weakenAt 0) (.inRight .word (.word value)) rhsStore)
    (latest : rhsStore.read? location = some (.inRight .unit carrier)) :
    ∃ output finalStore, ValueRel updated output ∧
      finalStore.read? location = some (.inRight .unit output) ∧
      Evaluates environment initialStore (Core.WordMapping.assign reference keyExpr rhs)
        (.inRight .word .unit) finalStore := by
  obtain ⟨words, rfl, rfl⟩ := related.canonical
  rw [insertEntries_of_insert words key value inserted]
  refine ⟨_, _, ValueRel.encode _, ?_,
    Core.WordMapping.assign_latest_evaluates words key value
      referenceEvaluated keyEvaluated rhsEvaluated latest⟩
  have inBounds : location < rhsStore.length := (List.getElem?_eq_some_iff.mp latest).choose
  have installedBounds : location <
      (Core.WordMapping.assignInsertStore rhsStore words key value location environment).length := by
    simpa [Core.WordMapping.assignInsertStore, Core.WordMapping.installedStore] using
      Nat.lt_succ_of_lt inBounds
  simp [Store.read?, installedBounds]

end Solcore.SourceSemantics.CoreLowering.WordMapping
end
