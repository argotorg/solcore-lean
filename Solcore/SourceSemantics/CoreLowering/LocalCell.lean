import Solcore.Frontend.SourceCoreLocalCell
import Solcore.SourceSemantics.CoreLowering.StagedValue
import Solcore.SourceSemantics.Dynamic.Fault

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
