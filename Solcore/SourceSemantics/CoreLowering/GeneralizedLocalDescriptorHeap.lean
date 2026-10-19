import Solcore.SourceSemantics.CoreLowering.GenericCellHeapOperations
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBundleReadMeaning
import Solcore.SourceSemantics.Dynamic.GeneralizedClosure

/-! A generalized local cell retains its complete Source descriptor and the
ordered instances created in its lexical context. Reads keep that context
separate from the current caller's context. Instance models supply static
code and capture representations; their laws concern typing and extension. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorHeap
open Core Frontend SourceInference TypeSystem GeneralHeap GenericHeap SourceCoreLocalPolymorphism

structure InstanceModel (definitions : Core.DataEnvironment) where
  locals : Catalog
  Origin : Dynamic.GeneralizedClosure → Binding → Substitution → Prop
  Represents : LocationMap → StoreTyping → Dynamic.GeneralizedClosure → Binding → Substitution →
    Instance → Core.Value → Prop
  runtime_hasType : ∀ {mapping world function binding active candidate value},
    Represents mapping world function binding active candidate value →
    RuntimeValueHasType world value candidate.type definitions
  extend : ∀ {mapping futureMapping world futureWorld function binding active candidate value},
    Represents mapping world function binding active candidate value →
    LocationMap.Extends mapping futureMapping → WorldExtends world futureWorld →
    Represents futureMapping futureWorld function binding active candidate value

variable {definitions : Core.DataEnvironment}

/-- The source capture and full original binding are retained once, before
any read supplies its own scheme evidence. Empty unused bundles are allowed. -/
inductive Stored (model : InstanceModel definitions) (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.GeneralizedClosure → Core.Value → Core.Ty → Prop where
  | bundle {function : Dynamic.GeneralizedClosure} (binding : Binding) (lexical : Substitution)
      (registered : model.locals.binding binding.caller binding.binder.id = .ok binding)
      (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
        function.captured function.binder function.initializer function)
      (origin : model.Origin function binding lexical)
      (binder : function.binder.id = binding.binder.id)
      (initializer : function.initializer = binding.initializer)
      {values : List Core.Value}
      (rows : ProductBundle.Pointwise
        (model.Represents mapping world function binding lexical) (binding.atContext lexical) values) :
      Stored model mapping world function (ProductBundle.value values) (binding.bundleType lexical)

private theorem bundle_typed {world : StoreTyping} {values : List Core.Value} {types : List Core.Ty}
    (typed : ProductBundle.Pointwise (fun value type => RuntimeValueHasType world value type definitions)
      values types) :
    RuntimeValueHasType world (ProductBundle.value values) (ProductBundle.type types) definitions := by
  induction typed with
  | nil => exact .unit
  | @cons value type values types related rows ih =>
      cases rows with
      | nil => exact related
      | cons next rest => exact .pair related ih

private theorem rows_typed {model : InstanceModel definitions}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.GeneralizedClosure}
    {binding : Binding} {lexical : Substitution} {entries : List Instance} {values : List Core.Value}
    (rows : ProductBundle.Pointwise (model.Represents mapping world function binding lexical) entries values) :
    ProductBundle.Pointwise (fun value type => RuntimeValueHasType world value type definitions)
      values (entries.map (·.type)) := by
  induction rows with
  | nil => exact .nil
  | cons head tail ih => exact .cons (model.runtime_hasType head) ih

private theorem rows_extend {model : InstanceModel definitions}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {entries : List Instance} {values : List Core.Value}
    (rows : ProductBundle.Pointwise (model.Represents mapping world function binding lexical) entries values)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ProductBundle.Pointwise (model.Represents futureMapping futureWorld function binding lexical) entries values := by
  induction rows with
  | nil => exact .nil
  | cons head tail ih => exact .cons (model.extend head maps worlds) ih

theorem Stored.runtime_hasType {model : InstanceModel definitions}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.GeneralizedClosure}
    {value : Core.Value} {payload : Core.Ty}
    (stored : Stored model mapping world function value payload) :
    RuntimeValueHasType world value payload definitions := by
  cases stored with
  | bundle binding lexical registered captures origin binder initializer rows =>
      exact bundle_typed (rows_typed rows)

theorem Stored.extend {model : InstanceModel definitions}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {value : Core.Value} {payload : Core.Ty}
    (stored : Stored model mapping world function value payload)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Stored model futureMapping futureWorld function value payload := by
  cases stored with
  | bundle binding lexical registered captures origin binder initializer rows =>
      exact Stored.bundle binding lexical registered captures origin binder initializer (rows_extend rows maps worlds)

inductive CellRepresents {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (ordinary : PayloadModel catalog projects definitions) (instances : InstanceModel definitions)
    (mapping : LocationMap) (world : StoreTyping) : Dynamic.Cell → Core.Value → Core.Ty → Prop where
  | ordinary {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
      (represented : GenericHeap.CellRepresents ordinary mapping world cell value payload) :
      CellRepresents ordinary instances mapping world cell value payload
  | generalized {function : Dynamic.GeneralizedClosure} {value : Core.Value} {payload : Core.Ty}
      (stored : Stored instances mapping world function value payload) :
      CellRepresents ordinary instances mapping world
        ⟨function.binder.scheme.body, none, some function⟩ (.inRight .unit value) payload

def cellModel {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (ordinary : PayloadModel catalog projects definitions) (instances : InstanceModel definitions) :
    CellModel definitions where
  Represents := CellRepresents ordinary instances
  runtime_hasType := by
    intro mapping world cell value payload represented
    cases represented with
    | ordinary prior => exact prior.runtime_hasType
    | generalized stored => exact .inRight stored.runtime_hasType
  extend := by
    intro mapping futureMapping world futureWorld cell value payload represented maps worlds
    cases represented with
    | ordinary prior => exact .ordinary (prior.extend maps worlds)
    | generalized stored => exact .generalized (stored.extend maps worlds)

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {ordinary : PayloadModel catalog projects definitions} {instances : InstanceModel definitions}

theorem initial {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Core.Store}
    (related : GenericHeap.HeapRepresents ordinary mapping world heap store) :
    CellHeapRepresents (cellModel ordinary instances) mapping world heap store :=
  (ordinaryHeap_iff.mpr related).includes (fun prior => CellRepresents.ordinary prior)

/-- Ordinary reads retain the original ordinary payload relation. The source
descriptor field, rather than a coincident native payload type, selects it. -/
theorem ordinary_cell {mapping : LocationMap} {world : StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (represented : CellRepresents ordinary instances mapping world cell value payload)
    (absent : cell.generalized = none) :
    GenericHeap.CellRepresents ordinary mapping world cell value payload := by
  cases represented with
  | ordinary prior => exact prior
  | generalized => cases absent

theorem ordinary_cells : OrdinaryCells ordinary (cellModel ordinary instances) where
  inject := CellRepresents.ordinary
  project := ordinary_cell

theorem descriptor_cell {mapping : LocationMap} {world : StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    {function : Dynamic.GeneralizedClosure}
    (represented : CellRepresents ordinary instances mapping world cell value payload)
    (descriptor : cell.generalized = some function) :
    cell = ⟨function.binder.scheme.body, none, some function⟩ ∧
      ∃ bundle, value = .inRight .unit bundle ∧ Stored instances mapping world function bundle payload := by
  cases represented with
  | ordinary prior => rw [prior.ordinary] at descriptor; cases descriptor
  | generalized stored =>
      cases descriptor
      exact ⟨rfl, _, rfl, stored⟩

/-- A genuine Source heap read recovers the corresponding stored descriptor
and its whole native instance row. No current-context filter is substituted. -/
theorem read {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Core.Store}
    {location : Dynamic.Location} {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure}
    (heaps : CellHeapRepresents (cellModel ordinary instances) mapping world heap store)
    (sourceRead : Dynamic.Heap.Reads heap location cell)
    (descriptor : cell.generalized = some function) :
    ∃ target bundle payload,
      ReferenceRepresents mapping world location target payload ∧
      store.read? target = some (.inRight .unit bundle) ∧
      Stored instances mapping world function bundle payload := by
  obtain ⟨target, value, payload, reference, found, represented⟩ := heaps.read sourceRead
  obtain ⟨_, bundle, same, stored⟩ := descriptor_cell represented descriptor
  exact ⟨target, bundle, payload, reference, same ▸ found, stored⟩

/-- Descriptor allocation follows the independent Source allocation rule and
allocates the native bundle at its own fresh location. -/
theorem allocate {mapping : LocationMap} {world : StoreTyping} {heap after : Dynamic.Heap}
    {store : Core.Store} {function : Dynamic.GeneralizedClosure} {location : Dynamic.Location}
    {bundle : Core.Value} {payload : Core.Ty}
    (heaps : CellHeapRepresents (cellModel ordinary instances) mapping world heap store)
    (stored : Stored instances mapping world function bundle payload)
    (allocated : Dynamic.Heap.AllocatesGeneralized heap function location after) :
    CellHeapRepresents (cellModel ordinary instances) (mapping ++ [store.length])
      (world ++ [OptionalCell.cellType payload]) after (store.allocate (.inRight .unit bundle)).1 ∧
    ReferenceRepresents (mapping ++ [store.length]) (world ++ [OptionalCell.cellType payload])
      location store.length payload :=
  heaps.allocate_generalized (CellRepresents.generalized stored) allocated

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorHeap
