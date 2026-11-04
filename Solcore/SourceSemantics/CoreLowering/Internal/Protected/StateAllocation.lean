import Solcore.SourceSemantics.CoreLowering.TypedGenericExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.SourceExecutionSize
import Solcore.SourceSemantics.CoreLowering.CoreEvaluationSize
import Solcore.SourceSemantics.CoreLowering.ExpressionFailurePostContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionContextualConstructors

/-!
# Protected contracts: state and allocation

`ProtectedStateTransition.Index`, the protected state and its bindings, ordinary, marked and cell allocation, and protected expression meaning.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedState
/-! Protected state is carried by an actual dependent witness. Expression
results relate that witness to the reached witness, so state created by a child
can be passed to the next child. The same index also covers lexical and body
states. Administrative transport preserves the complete record observation.
These contracts use the existing Source and Core grades and supply no execution
theorem or induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof

universe u v

structure Index where
  scope : SourceCoreLocalCell.Scope
  mapping : LocationMap
  world : StoreTyping
  heap : Dynamic.Heap
  store : Store
  canonical : Environment

def Index.extend (initial : Index) (mapping : LocationMap) (world : StoreTyping)
    (heap : Dynamic.Heap) (store : Store) : Index :=
  { initial with mapping := mapping, world := world, heap := heap, store := store }

/-- A relation keeps its concrete endpoint witnesses. Its record observation
may, for example, be all ordered record lists in an authority pool. -/
structure Protocol (Records : Type v) where
  State : Index → Type u
  records : {index : Index} → State index → Records
  Relates : {initial reached : Index} → State initial → State reached → Prop
  refl : ∀ {index} (state : State index), Relates state state
  trans : ∀ {initial middle reached} {first : State initial} {second : State middle}
    {last : State reached}, Relates first second → Relates second last → Relates first last

variable {Records : Type v} (protocol : Protocol.{u, v} Records)

def entry : SourceCoreLocalCell.Scope → LocationMap → StoreTyping →
    Dynamic.Heap → Store → Environment → Prop :=
  fun scope mapping world heap store canonical =>
    Nonempty (protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)

/-- The reached witness is retained together with its relation to this input. -/
def Transition {initial : Index} (state : protocol.State initial) (reached : Index) : Prop :=
  ∃ final : protocol.State reached, protocol.Relates state final

theorem Transition.refl {index : Index} (state : protocol.State index) :
    Transition protocol state index := ⟨state, protocol.refl state⟩

theorem Transition.of_related {initial reached : Index}
    {state : protocol.State initial} {final : protocol.State reached}
    (related : protocol.Relates state final) : Transition protocol state reached :=
  ⟨final, related⟩

theorem Transition.entry {initial reached : Index} {state : protocol.State initial}
    (transition : Transition protocol state reached) :
    entry protocol reached.scope reached.mapping reached.world reached.heap reached.store reached.canonical := by
  obtain ⟨final, _⟩ := transition
  exact ⟨final⟩

/-- Sequential composition consumes the actual first post-witness. -/
theorem Transition.then {initial middle reached : Index} {state : protocol.State initial}
    (first : Transition protocol state middle)
    (next : ∀ final : protocol.State middle, protocol.Relates state final →
      Transition protocol final reached) : Transition protocol state reached := by
  obtain ⟨middleState, related⟩ := first
  obtain ⟨final, last⟩ := next middleState related
  exact ⟨final, protocol.trans related last⟩

/-- Ordinary administrative effects transport one witness and preserve its
complete record observation. Record-producing transitions are proved directly
with `Protocol.Relates`, rather than defined by this transport operation. -/
structure AdministrativeTransport where
  extend : ∀ {initial : Index} (_state : protocol.State initial)
    {mapping world heap store},
    LocationMap.Extends initial.mapping mapping → WorldExtends initial.world world →
    AdministrativePreserved initial.mapping initial.store mapping store →
    Dynamic.HeapMetadataExtend initial.heap heap →
    protocol.State (initial.extend mapping world heap store)
  related : ∀ {initial : Index} (state : protocol.State initial)
    {mapping world heap store}
    (maps : LocationMap.Extends initial.mapping mapping) (worlds : WorldExtends initial.world world)
    (frame : AdministrativePreserved initial.mapping initial.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend initial.heap heap),
    protocol.Relates state (extend state maps worlds frame metadata)
  records_eq : ∀ {initial : Index} (state : protocol.State initial)
    {mapping world heap store}
    (maps : LocationMap.Extends initial.mapping mapping) (worlds : WorldExtends initial.world world)
    (frame : AdministrativePreserved initial.mapping initial.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend initial.heap heap),
    protocol.records (extend state maps worlds frame metadata) = protocol.records state

/-- A protocol whose witnesses survive replacing the canonical values of the
lexical slots, keeping every slot past the scope. A closure entry needs it after
copying the captured cells, which rebinds the scope's slots to the copies. -/
def Rebinds : Prop :=
  ∀ {index : Index} (state : protocol.State index) (canonical : Environment),
    (∀ slot, index.scope.length ≤ slot → canonical[slot]? = index.canonical[slot]?) →
    Transition protocol state { index with canonical := canonical }

theorem AdministrativeTransport.transition (transport : AdministrativeTransport protocol)
    {initial : Index} (state : protocol.State initial) {mapping world heap store}
    (maps : LocationMap.Extends initial.mapping mapping) (worlds : WorldExtends initial.world world)
    (frame : AdministrativePreserved initial.mapping initial.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend initial.heap heap) :
    Transition protocol state (initial.extend mapping world heap store) :=
  ⟨transport.extend state maps worlds frame metadata, transport.related state maps worlds frame metadata⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateBindings
/-! Lexical binders reindex the concrete reached state. The source-visible
payload reference is prepended and later removed; heap and native store stay
fixed. Both operations preserve the complete record observation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
open Core Frontend SourceInference
universe u v

def Index.prepend (index : Index) (id : Resolved.LocalId) (type : Ty) (value : Value) : Index :=
  { index with scope := (id, type) :: index.scope, canonical := value :: index.canonical }

/-- These operations concern the actual canonical source binder. Hidden Core
slots continue to use the existing renaming and do not reindex this state. -/
structure Bindings {Records : Type v} (protocol : Protocol.{u, v} Records) where
  prepend : ∀ {index : Index} (_state : protocol.State index) (id : Resolved.LocalId)
    (type : Ty) (value : Value), protocol.State (index.prepend id type value)
  prepend_related : ∀ {index : Index} (state : protocol.State index) (id : Resolved.LocalId)
    (type : Ty) (value : Value), protocol.Relates state (prepend state id type value)
  prepend_records : ∀ {index : Index} (state : protocol.State index) (id : Resolved.LocalId)
    (type : Ty) (value : Value), protocol.records (prepend state id type value) = protocol.records state
  restore : ∀ {index : Index} {id : Resolved.LocalId} {type : Ty} {value : Value},
    protocol.State (index.prepend id type value) → protocol.State index
  restore_related : ∀ {index : Index} {id : Resolved.LocalId} {type : Ty} {value : Value}
    (state : protocol.State (index.prepend id type value)), protocol.Relates state (restore state)
  restore_records : ∀ {index : Index} {id : Resolved.LocalId} {type : Ty} {value : Value}
    (state : protocol.State (index.prepend id type value)), protocol.records (restore state) = protocol.records state

variable {Records : Type v} {protocol : Protocol.{u, v} Records} (bindings : Bindings protocol)

include bindings in
theorem Bindings.prepend_transition {index : Index} (state : protocol.State index)
    (id : Resolved.LocalId) (type : Ty) (value : Value) :
    Transition protocol state (index.prepend id type value) :=
  ⟨bindings.prepend state id type value, bindings.prepend_related state id type value⟩

include bindings in
theorem Bindings.restore_transition {index : Index} {id : Resolved.LocalId} {type : Ty} {value : Value}
    (state : protocol.State (index.prepend id type value)) : Transition protocol state index :=
  ⟨bindings.restore state, bindings.restore_related state⟩

include bindings in
/-- Removing a binder consumes the child's reached witness, so any records
created inside the lexical suffix remain in the returned state. -/
theorem Bindings.restore_reached {initial reached : Index} (state : protocol.State initial)
    {id : Resolved.LocalId} {type : Ty} {value : Value}
    (transition : Transition protocol state (reached.prepend id type value)) :
    Transition protocol state reached := by
  obtain ⟨final, related⟩ := transition
  exact ⟨bindings.restore final, protocol.trans related (bindings.restore_related final)⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateOrdinaryAllocation
/-! A marked allocation producer retains the ordinary execution and heap
receipts together with its concrete protected post-witness. Readiness concerns
the selected live authority and its history; it contains no body execution law.
The administrative implementation has an unchanged record observation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.OrdinaryAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion
universe u v

variable {Records : Type v}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}

structure Producer (protocol : Protocol.{u, v} Records)
    (layouts : SourceCoreAllocationLayouts.Prepared) (layout : SourceCoreCallableIndexedFrames.Layout)
    (model : GenericHeap.PayloadModel catalog projects nativeDefinitions) where
  Ready : {index : Index} → protocol.State index → Location → NativeFrame → Prop
  complete : ∀ {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (_same : annotation.original = allocation.expression)
    (_definitions : layouts.definitions = nativeDefinitions) (_registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {contextLocation : Location} {native : NativeFrame}
    {payload : Option Value} {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}
    (_environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope environment canonical nativeDefinitions)
    (_agrees : EnvironmentsAgree request.references canonical actual)
    (_heaps : GenericHeap.HeapRepresents model mapping world before store)
    (_reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (_payloadAt : PayloadAt request actual payload)
    (_cell : GenericHeap.CellRepresents model mapping world
      ⟨request.binder.scheme.body, sourceValue, none⟩ (optionalValue request.payloadType payload) request.payloadType)
    (_allocated : Dynamic.Heap.Allocates before request.binder.scheme.body sourceValue sourceLocation after)
    (initial : protocol.State ⟨request.scope, mapping, world, before, store, canonical⟩)
    (_ready : Ready initial contextLocation native),
    ∃ captured,
      Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope) nativeDefinitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved mapping store (mapping ++ [store.length + 2])
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      Transition protocol initial
        ⟨(request.binder.id, request.payloadType) :: request.scope, mapping ++ [store.length + 2],
          world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType], after,
          store ++ [SourceCoreCallableIndexedFrames.encode layout native,
            SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload],
          .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical⟩

def of_administrative (protocol : Protocol.{u, v} Records)
    (transport : AdministrativeTransport protocol) (bindings : Bindings protocol)
    (layouts : SourceCoreAllocationLayouts.Prepared) (layout : SourceCoreCallableIndexedFrames.Layout)
    (model : GenericHeap.PayloadModel catalog projects nativeDefinitions) : Producer protocol layouts layout model where
  Ready _ _ _ := True
  complete := by
    intro owner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native payload sourceValue sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial _
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame⟩ :=
      CallableIndexedOrdinaryAllocation.preserves_with_captures allocation annotation same definitions registered
        environments agrees heaps reference read payloadAt cell allocated
    let extended := transport.extend initial
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
      (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType]) from ⟨_, rfl⟩)
      frame (Dynamic.HeapMetadataExtend.of_allocation allocated)
    refine ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      bindings.prepend extended request.binder.id request.payloadType
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)), ?_⟩
    exact protocol.trans
      (transport.related initial _ _ frame (Dynamic.HeapMetadataExtend.of_allocation allocated))
      (bindings.prepend_related extended _ _ _)

/-- The original allocator API has no protected data; its wrapper uses a
constant proof witness and then forgets the added transition. -/
def unitProtocol : Protocol Unit where
  State _ := Unit
  records _ := ()
  Relates _ _ := True
  refl _ := True.intro
  trans _ _ := True.intro

def unitTransport : AdministrativeTransport unitProtocol where
  extend := fun {_initial} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata => ()
  related := fun {_initial} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata => True.intro
  records_eq := fun {_initial} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata => rfl

private def unitBindings : Bindings unitProtocol where
  prepend _ _ _ _ := ()
  prepend_related _ _ _ _ := True.intro
  prepend_records _ _ _ _ := rfl
  restore _ := ()
  restore_related _ := True.intro
  restore_records _ := rfl

theorem unitRebinds : Rebinds unitProtocol := fun _state _canonical _slots => ⟨(), True.intro⟩

def unitProducer (layouts : SourceCoreAllocationLayouts.Prepared) (layout : SourceCoreCallableIndexedFrames.Layout)
    (model : GenericHeap.PayloadModel catalog projects nativeDefinitions) : Producer unitProtocol layouts layout model :=
  of_administrative unitProtocol unitTransport unitBindings layouts layout model

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.OrdinaryAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateMarkedAllocation
/-! Marked allocation retains the independent source cell type even when the
compiler erases the marker binder type. The actual snapshot, captures, payload
cell and reached state remain the same ordinary Core allocation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.MarkedAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion
universe u v
variable {Records : Type v}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}

structure Producer (protocol : Protocol.{u, v} Records)
    (layouts : SourceCoreAllocationLayouts.Prepared) (layout : SourceCoreCallableIndexedFrames.Layout)
    (model : GenericHeap.PayloadModel catalog projects nativeDefinitions) where
  Ready : {index : Index} → protocol.State index → Location → NativeFrame → Prop
  complete : ∀ {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (_same : annotation.original = allocation.expression)
    (_definitions : layouts.definitions = nativeDefinitions) (_registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {contextLocation : Location} {native : NativeFrame}
    {sourceType : TypeSystem.Ty} {payload : Option Value} {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}
    (_environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope environment canonical nativeDefinitions)
    (_agrees : EnvironmentsAgree request.references canonical actual)
    (_heaps : GenericHeap.HeapRepresents model mapping world before store)
    (_reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (_payloadAt : PayloadAt request actual payload)
    (_cell : GenericHeap.CellRepresents model mapping world
      ⟨sourceType, sourceValue, none⟩ (optionalValue request.payloadType payload) request.payloadType)
    (_allocated : Dynamic.Heap.Allocates before sourceType sourceValue sourceLocation after)
    (initial : protocol.State ⟨request.scope, mapping, world, before, store, canonical⟩)
    (_ready : Ready initial contextLocation native),
    ∃ captured,
      Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope) nativeDefinitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved mapping store (mapping ++ [store.length + 2])
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      Transition protocol initial
        ⟨(request.binder.id, request.payloadType) :: request.scope, mapping ++ [store.length + 2],
          world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType], after,
          store ++ [SourceCoreCallableIndexedFrames.encode layout native,
            SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload],
          .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical⟩

/-- The compatibility producer observes the actual proved administrative effects.
It preserves the complete input record observation and adds no snapshot record. -/
def of_administrative (protocol : Protocol.{u, v} Records)
    (transport : AdministrativeTransport protocol) (bindings : Bindings protocol)
    (layouts : SourceCoreAllocationLayouts.Prepared) (layout : SourceCoreCallableIndexedFrames.Layout)
    (model : GenericHeap.PayloadModel catalog projects nativeDefinitions) : Producer protocol layouts layout model where
  Ready _ _ _ := True
  complete := by
    intro owner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceType payload sourceValue sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial _ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame⟩ :=
      CallableIndexedOrdinaryAllocation.preserves_with_captures_for_type allocation annotation same definitions registered
        environments agrees heaps reference read payloadAt cell allocated
    let extended := transport.extend initial
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
      (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType]) from ⟨_, rfl⟩)
      frame (Dynamic.HeapMetadataExtend.of_allocation allocated)
    refine ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      bindings.prepend extended request.binder.id request.payloadType
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)), ?_⟩
    exact protocol.trans
      (transport.related initial _ _ frame (Dynamic.HeapMetadataExtend.of_allocation allocated))
      (bindings.prepend_related extended _ _ _)

/-- A source binder is the declaration-type instance of the same producer. -/
def Producer.toOrdinary {protocol : Protocol.{u, v} Records}
    {layouts : SourceCoreAllocationLayouts.Prepared} {layout : SourceCoreCallableIndexedFrames.Layout}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    (producer : Producer protocol layouts layout model) :
    OrdinaryAllocation.Producer protocol layouts layout model where
  Ready := producer.Ready
  complete := by
    intro owner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native payload sourceValue sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial ready
    exact producer.complete allocation annotation same definitions registered
      environments agrees heaps reference read payloadAt cell allocated initial ready

/-- Constant observation compatibility forgets only the reached witness. -/
def unitProducer (layouts : SourceCoreAllocationLayouts.Prepared) (layout : SourceCoreCallableIndexedFrames.Layout)
    (model : GenericHeap.PayloadModel catalog projects nativeDefinitions) :
    Producer OrdinaryAllocation.unitProtocol layouts layout model where
  Ready _ _ _ := True
  complete := by
    intro owner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceType payload sourceValue sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial _ready
    obtain ⟨captured, captures, typed, evaluated, finalHeaps, finalReference, frame⟩ :=
      CallableIndexedOrdinaryAllocation.preserves_with_captures_for_type allocation annotation same definitions registered
        environments agrees heaps reference read payloadAt cell allocated
    exact ⟨captured, captures, typed, evaluated, finalHeaps, finalReference, frame, (), True.intro⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.MarkedAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateAllocationReadiness
/-! The lexical tree uses one fixed physical frame and stable native token.
Every allocation consumes its actual reached-state witness and a real live
read. Readiness is supplied by a logical acquisition family, independently of
source/native expression or body execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.OrdinaryAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory
universe u v

variable {Records : Type v} {protocol : Protocol.{u, v} Records}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
  {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
  {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}

def ReadyAt (producer : Producer protocol layouts frame model)
    (location : Location) (native : NativeFrame) : Prop :=
  ∀ {index : Index} (reached : protocol.State index),
    index.store.read? location = some (SourceCoreCallableIndexedFrames.encode frame native) →
    producer.Ready reached location native

/-- The certified administrative effect supplies the reached read, including
after expression children and completed source allocations. -/
theorem ReadyAt.after_administrative {producer : Producer protocol layouts frame model}
    {location : Location} {native : NativeFrame}
    (ready : ReadyAt producer location native)
    {initial reached : Index} (state : protocol.State reached)
    (read : initial.store.read? location = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : location ∉ initial.mapping)
    (preserved : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    producer.Ready state location native := by
  exact ready state ((preserved location unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)

theorem administrative_readyAt (protocol : Protocol.{u, v} Records)
    (transport : AdministrativeTransport protocol) (bindings : Bindings protocol)
    (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (model : GenericHeap.PayloadModel catalog projects nativeDefinitions)
    (location : Location) (native : NativeFrame) :
    ReadyAt (of_administrative protocol transport bindings layouts frame model) location native :=
  fun _state _read => True.intro

theorem unit_readyAt (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (model : GenericHeap.PayloadModel catalog projects nativeDefinitions)
    (location : Location) (native : NativeFrame) :
    ReadyAt (unitProducer layouts frame model) location native :=
  fun _state _read => True.intro

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.OrdinaryAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedReadyExpressionFaultPostContracts
/-! Actual ready children retain a fault post at the same returned tuple.
These contracts supply no execution or chosen primitive witness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedReadyExpressionFaultPostContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open ProtectedStateTransition
open GenericExpressionMeaning (Certificate FaultRep)
universe u v

abbrev SourceTrace := Program → Nat → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
  TypedSource → Dynamic.Environment → Dynamic.Heap → ExpressionId → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop

def ExpressionPreservesAt (traceAt : SourceTrace) {Records : Type v} (protocol : Protocol.{u, v} Records) (ready : ∀ {index : ProtectedStateTransition.Index}, protocol.State index → Prop) (post : ExpressionFailurePostContracts.ExpressionFaultPost) (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    ready initial →
    traceAt program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      (∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ∀ sourceValue, outcome = .value sourceValue → ready reached) ∧
      ExpressionFailurePostContracts.OutcomePost post program context evidence source environment before id
        lowered.type outcome after value finalMap finalWorld finalStore

def ExpressionReflectsAt (traceAt : SourceTrace) {Records : Type v} (protocol : Protocol.{u, v} Records) (ready : ∀ {index : ProtectedStateTransition.Index}, protocol.State index → Prop) (post : ExpressionFailurePostContracts.ExpressionFaultPost) (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    ready initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      traceAt program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      (∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ∀ sourceValue, outcome = .value sourceValue → ready reached) ∧
      ExpressionFailurePostContracts.OutcomePost post program context evidence source environment before id
        lowered.type outcome after value finalMap finalWorld finalStore

end Solcore.SourceSemantics.CoreLowering.ProtectedReadyExpressionFaultPostContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning
/-! Recursive expression meanings with a protected administrative entry.
The entry concerns the canonical environment and real store. Temporary actual
slots are tracked by the existing renaming, while successful child effects
transport the entry along real heap/world extensions and protected writes.
An entry contains no source execution or body meaning.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open GenericExpressionMeaning (Certificate FaultRep ResultRepresents)

abbrev Entry := SourceCoreLocalCell.Scope → LocationMap → StoreTyping →
  Dynamic.Heap → Store → Environment → Prop

/-- The exact administrative observations survive the effects already
certified by expression meaning. Actual temporary binders leave this canonical
environment unchanged. -/
structure Transport (entry : Entry) : Prop where
  extend : ∀ {scope mapping world before store canonical futureMap futureWorld after futureStore},
    entry scope mapping world before store canonical →
    LocationMap.Extends mapping futureMap → WorldExtends world futureWorld →
    AdministrativePreserved mapping store futureMap futureStore →
    Dynamic.HeapMetadataExtend before after →
    entry scope futureMap futureWorld after futureStore canonical

def Preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) (entry : Entry) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def Reflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) (entry : Entry) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    Evaluates actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

theorem preserves_of_typed
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
    (entry : Entry)
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults) :
    Preserves model program context evidence source certificate faults entry := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed _ trace
  exact meaning certified found environments heaps locals agrees typed trace

theorem reflects_of_typed
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
    (entry : Entry)
    (meaning : TypedGenericExpressionMeaning.Reflects model program context evidence source certificate faults) :
    Reflects model program context evidence source certificate faults entry := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed _ evaluated
  exact meaning certified found environments heaps locals agrees typed evaluated

end Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning

-- Protected ordered argument composition.
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedDataExpressionSequence
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open GenericExpressionMeaning (Certificate FaultRep agree_prefix rename_prefix)
open DataPatternValues DataExpressionSequence


/-- An outcome wrapper around the existing measured source judgment. -/
inductive ExpressionTraceAt (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (id : ExpressionId) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {value after} (trace : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before id value after) :
      ExpressionTraceAt program size context evidence source environment before id (.value value) after
  | fault {reason after} (trace : SourceExecutionSize.ExpressionFaults program size context evidence source environment before id reason after) :
      ExpressionTraceAt program size context evidence source environment before id (.fault reason) after

theorem ExpressionTraceAt.sound {program size context evidence source environment before id outcome after}
    (trace : ExpressionTraceAt program size context evidence source environment before id outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | value trace => exact .value trace.sound
  | fault trace => exact .fault trace.sound

theorem ExpressionTraceAt.has_size {program context evidence source environment before id outcome after}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    ∃ size, ExpressionTraceAt program size context evidence source environment before id outcome after := by
  cases trace with
  | value trace => obtain ⟨size, sized⟩ := SourceExecutionSize.ExpressionEvaluates.has_size trace; exact ⟨size, .value sized⟩
  | fault trace => obtain ⟨size, sized⟩ := SourceExecutionSize.ExpressionFaults.has_size trace; exact ⟨size, .fault sized⟩

inductive TraceAt (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (ids : List ExpressionId) : Outcome → Dynamic.Heap → Prop where
  | values {values after} (trace : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment before ids values after) :
      TraceAt program size context evidence source environment before ids (.ok values) after
  | fault {reason after} (trace : SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after) :
      TraceAt program size context evidence source environment before ids (.error reason) after

theorem TraceAt.sound {program size context evidence source environment before ids outcome after}
    (trace : TraceAt program size context evidence source environment before ids outcome after) :
    Trace program context evidence source environment before ids outcome after := by
  cases trace with
  | values trace => exact .values trace.sound
  | fault trace => exact .fault trace.sound

theorem TraceAt.has_size {program context evidence source environment before ids outcome after}
    (trace : Trace program context evidence source environment before ids outcome after) :
    ∃ size, TraceAt program size context evidence source environment before ids outcome after := by
  cases trace with
  | values trace => obtain ⟨size, sized⟩ := SourceExecutionSize.ExpressionsEvaluate.has_size trace; exact ⟨size, .values sized⟩
  | fault trace => obtain ⟨size, sized⟩ := SourceExecutionSize.ExpressionsFault.has_size trace; exact ⟨size, .fault sized⟩

def ExpressionPreservesAt (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) (entry : ProtectedExpressionMeaning.Entry) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    ExpressionTraceAt program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def ExpressionReflectsAt (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) (entry : ProtectedExpressionMeaning.Entry) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      ExpressionTraceAt program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after
/-! Ordered composition threads actual protected-state witnesses through the
same source/native children and the existing static sequence tree. -/
namespace Stateful
open ProtectedStateTransition (Protocol Transition)
universe u v

def ExpressionPreservesAt {Records : Type v} (protocol : Protocol.{u, v} Records) (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    ExpressionTraceAt program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def ExpressionReflectsAt {Records : Type v} (protocol : Protocol.{u, v} Records) (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      ExpressionTraceAt program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

/-! The same ordered sequence proof cores carry an actual readiness receipt.
Readiness is required at input and retained only for successful children. -/
namespace WithReady

def ExpressionPreservesAt {Records : Type v} (protocol : Protocol.{u, v} Records) (ready : ∀ {index : ProtectedStateTransition.Index}, protocol.State index → Prop) (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    ready initial →
    ExpressionTraceAt program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ∀ sourceValue, outcome = .value sourceValue → ready reached

def ExpressionReflectsAt {Records : Type v} (protocol : Protocol.{u, v} Records) (ready : ∀ {index : ProtectedStateTransition.Index}, protocol.State index → Prop) (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    ready initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      ExpressionTraceAt program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ∀ sourceValue, outcome = .value sourceValue → ready reached

variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (ready : ∀ {index : ProtectedStateTransition.Index}, protocol.State index → Prop)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}

theorem preserves_values_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ id, id ∈ ids → ∀ size, size < budget →
      ExpressionPreservesAt protocol ready size model program context evidence source
        (fun current expression code => expression = id ∧ certificate current expression code) faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : ready initial)
    {size : Nat}
    (execution : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment before ids sources after) (bounded : size ≤ budget) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ready reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ sources after with
  | nil =>
    cases execution
    exact ⟨[], store, mapping, world, .inRight .unit, .nil, heaps,
      .refl _, .refl _, .refl _ _, .refl _, ⟨initial, protocol.refl initial, initialReady⟩⟩
  | single found generated =>
    cases execution with
    | cons head tail =>
      cases tail
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, transition⟩ := meaning _ (by simp) _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded) ⟨rfl, generated⟩ found environments heaps locals layout actualTyped initial initialReady (.value head)
      cases represented with
      | value payload =>
        exact ⟨[_], finalStore, finalMap, finalWorld, evaluated, .cons payload .nil,
          finalHeaps, maps, worlds, frame, metadata, by obtain ⟨reached, related, finalReady⟩ := transition; exact ⟨reached, related, finalReady _ rfl⟩⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | cons head rest =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        meaning _ (by simp) _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded) ⟨rfl, generated⟩ found environments heaps locals layout actualTyped initial initialReady (.value head)
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
        obtain ⟨values, finalStore, finalMap, finalWorld, second, restRep, finalHeaps,
          maps, worlds, frame, metadata, lastTransition⟩ := ih
            (fun child member => meaning child (List.mem_cons_of_mem _ member))
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix layout coreValue)
            (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
            middleState (firstReady _ rfl) rest
            (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded)
        obtain ⟨finalState, lastRelated, lastReady⟩ := lastTransition
        have nonempty : values ≠ [] := by
          intro absent
          have lengths := restRep.length.2
          simp [absent] at lengths
        refine ⟨coreValue :: values, finalStore, finalMap, finalWorld, ?_,
          .cons (model.extend payload maps worlds) restRep, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
          ⟨finalState, protocol.trans firstRelated lastRelated, lastReady⟩⟩
        rw [rename_prefix] at second
        have combined := LocalSequence.pair_success lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first second
        simpa [SourceCoreCalls.packArguments, pair_rename, packValues, nonempty] using combined

theorem preserves_fault_bounded_with_post
    (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (listPost : ExpressionFailurePostContracts.ExpressionsFaultPost)
    (joins : ExpressionFailurePostContracts.SequenceJoins expressionPost listPost program context evidence source)
    (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ id, id ∈ ids → ∀ size, size < budget →
      ProtectedReadyExpressionFaultPostContracts.ExpressionPreservesAt ExpressionTraceAt protocol ready expressionPost size model program context evidence source
        (fun current expression code => expression = id ∧ certificate current expression code) faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : ready initial)
    {size : Nat}
    (execution : SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      listPost program context evidence source environment before ids reason after token finalMap finalWorld finalStore := by
  induction tree generalizing size mapping world actual actualContext before store ξ after with
  | nil => cases execution
  | single found generated =>
    cases execution with
    | head failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, transition, childPost⟩ := meaning _ (by simp) _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded) ⟨rfl, generated⟩ found environments heaps locals layout actualTyped initial initialReady (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, evaluated, matched,
          finalHeaps, maps, worlds, frame, metadata, by obtain ⟨reached, related, _⟩ := transition; exact ⟨reached, related⟩, joins.head failed.sound (ExpressionFailurePostContracts.OutcomePost.fault childPost)⟩
    | tail _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | head failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, transition, childPost⟩ := meaning _ (by simp) _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded) ⟨rfl, generated⟩ found environments heaps locals layout actualTyped initial initialReady (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps, worlds, frame, metadata, by obtain ⟨reached, related, _⟩ := transition; exact ⟨reached, related⟩, joins.head failed.sound (ExpressionFailurePostContracts.OutcomePost.fault childPost)⟩
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_left_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type evaluated
    | tail head failed =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition, _firstPost⟩ :=
        meaning _ (by simp) _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded) ⟨rfl, generated⟩ found environments heaps locals layout actualTyped initial initialReady (.value head)
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
        obtain ⟨token, finalStore, finalMap, finalWorld, second, matched, finalHeaps,
          maps, worlds, frame, metadata, lastTransition, tailPost⟩ := ih
            (fun child member => meaning child (List.mem_cons_of_mem _ member))
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix layout coreValue)
            (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
            middleState (firstReady _ rfl) failed
            (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded)
        obtain ⟨finalState, lastRelated⟩ := lastTransition
        refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
          ⟨finalState, protocol.trans firstRelated lastRelated⟩, joins.tail head.sound failed.sound tailPost⟩
        rw [rename_prefix] at second
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_right_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first second

theorem reflects_bounded_with_post
    (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (listPost : ExpressionFailurePostContracts.ExpressionsFaultPost)
    (joins : ExpressionFailurePostContracts.SequenceJoins expressionPost listPost program context evidence source)
    (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ id, id ∈ ids → ∀ size, size < budget →
      ProtectedReadyExpressionFaultPostContracts.ExpressionReflectsAt ExpressionTraceAt protocol ready expressionPost size model program context evidence source
        (fun current expression code => expression = id ∧ certificate current expression code) faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : ready initial)
    {size : Nat}
    (evaluated : EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) (bounded : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      TraceAt program sourceSize context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      (∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ∀ sources, outcome = .ok sources → ready reached) ∧
      ExpressionFailurePostContracts.ListOutcomePost listPost program context evidence source environment before ids
        (SourceCoreCalls.packArguments codes).type outcome after value finalMap finalWorld finalStore := by
  induction tree generalizing size mapping world actual actualContext before store ξ value finalStore with
  | nil =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (show Evaluates actual store
      ((SourceCoreCalls.packArguments []).expression.rename ξ) (.inRight .word .unit) store from .inRight .unit)
    exact ⟨_, .ok [], before, mapping, world, .values .nil, .values (values := []) .nil, heaps,
      .refl _, .refl _, .refl _ _, .refl _, ⟨initial, protocol.refl initial, fun _ _ => initialReady⟩, True.intro⟩
  | single found generated =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
      maps, worlds, frame, metadata, transition, childPost⟩ := meaning _ (by simp) _ (by omega) ⟨rfl, generated⟩ found environments heaps locals layout actualTyped initial initialReady evaluated
    cases represented with
    | value payload =>
      cases execution with
      | value trace => exact ⟨_, .ok [_], after, finalMap, finalWorld,
          .values (.cons trace .nil), .values (values := [_]) (.cons payload .nil), finalHeaps, maps, worlds, frame, metadata, by obtain ⟨reached, related, finalReady⟩ := transition; exact ⟨reached, related, fun _ _ => finalReady _ rfl⟩, True.intro⟩
    | fault matched =>
      cases execution with
      | fault trace => exact ⟨_, .error _, after, finalMap, finalWorld,
          .fault (.head trace), .fault matched, finalHeaps, maps, worlds, frame, metadata, by obtain ⟨reached, related, _⟩ := transition; exact ⟨reached, related, fun _ impossible => nomatch impossible⟩, ⟨_, rfl, joins.head trace.sound (ExpressionFailurePostContracts.OutcomePost.fault childPost)⟩⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    change EvaluationSize size actual store ((LocalSequence.pair lowered.type
      (SourceCoreCalls.packArguments (nextCode :: codes)).type lowered.expression
      (SourceCoreCalls.packArguments (nextCode :: codes)).expression).rename ξ) value finalStore at evaluated
    rw [pair_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft first _ =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
        maps, worlds, frame, metadata, transition, childPost⟩ := meaning _ (by simp) _ (by omega) ⟨rfl, generated⟩ found environments heaps locals layout actualTyped initial initialReady first
      cases represented with
      | fault matched =>
        cases execution with
        | fault trace =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound (LocalSequence.pair_left_failure lowered.type
            (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound)
          exact ⟨_, .error _, after, finalMap, finalWorld, .fault (.head trace), .fault matched,
            finalHeaps, maps, worlds, frame, metadata, by obtain ⟨reached, related, _⟩ := transition; exact ⟨reached, related, fun _ impossible => nomatch impossible⟩, ⟨_, rfl, joins.head trace.sound (ExpressionFailurePostContracts.OutcomePost.fault childPost)⟩⟩
    | caseRight first continuation =>
      obtain ⟨sourceSize, outcome, middle, middleMap, middleWorld, execution, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition, _firstPost⟩ :=
        meaning _ (by simp) _ (by omega) ⟨rfl, generated⟩ found environments heaps locals layout actualTyped initial initialReady first
      cases represented with
      | @value sourceValue coreValue payload =>
        rename_i middleStore coreValue
        obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
        have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical
            (coreValue :: actual) := agree_prefix layout coreValue
        cases execution with
        | value firstSource =>
          cases continuation with
          | caseLeft second _ =>
            have shifted := second
            rw [← rename_prefix] at shifted
            obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, result, finalHeaps,
              maps, worlds, frame, metadata, lastTransition, tailPost⟩ := ih
                (fun child member => meaning child (List.mem_cons_of_mem _ member))
                (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) nextLayout
                (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                middleState (firstReady _ rfl) shifted (by omega)
            obtain ⟨finalState, lastRelated, lastReady⟩ := lastTransition
            cases result with
            | fault matched =>
              cases sourceTrace with
              | fault tailSource =>
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                  (LocalSequence.pair_right_failure lowered.type
                    (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound second.sound)
                exact ⟨_, .error _, after, finalMap, finalWorld, .fault (.tail firstSource tailSource), .fault matched,
                  finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans metadata,
                  ⟨finalState, protocol.trans firstRelated lastRelated, lastReady⟩, ⟨_, rfl, joins.tail firstSource.sound tailSource.sound (ExpressionFailurePostContracts.ListOutcomePost.fault tailPost)⟩⟩
          | caseRight second _ =>
            have shifted := second
            rw [← rename_prefix] at shifted
            obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, result, finalHeaps,
              maps, worlds, frame, metadata, lastTransition, tailPost⟩ := ih
                (fun child member => meaning child (List.mem_cons_of_mem _ member))
                (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) nextLayout
                (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                middleState (firstReady _ rfl) shifted (by omega)
            obtain ⟨finalState, lastRelated, lastReady⟩ := lastTransition
            cases result with
            | @values sources values restRep =>
              cases sourceTrace with
              | values tailSource =>
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                  (LocalSequence.pair_success lowered.type
                    (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound second.sound)
                have nonempty : values ≠ [] := by
                  intro absent
                  have lengths := restRep.length.2
                  simp [absent] at lengths
                refine ⟨_, .ok (sourceValue :: sources), after, finalMap, finalWorld,
                  .values (.cons firstSource tailSource), ?_, finalHeaps,
                  firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans metadata,
                  ⟨finalState, protocol.trans firstRelated lastRelated, fun _ _ => lastReady _ rfl⟩, True.intro⟩
                simpa [packValues, nonempty] using
                  Result.values (codes := lowered :: nextCode :: codes)
                    (.cons (model.extend payload maps worlds) restRep)

private theorem preserves_child_trivial_post {size : Nat}
    (meaning : ExpressionPreservesAt protocol ready size model program context evidence source certificate faults) :
    ProtectedReadyExpressionFaultPostContracts.ExpressionPreservesAt ExpressionTraceAt protocol ready
      ExpressionFailurePostContracts.TrivialExpressionPost size model program context evidence source certificate faults := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ := meaning certified found environments heaps locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, transition, ExpressionFailurePostContracts.OutcomePost.of_trivial represented⟩

private theorem reflects_child_trivial_post {size : Nat}
    (meaning : ExpressionReflectsAt protocol ready size model program context evidence source certificate faults) :
    ProtectedReadyExpressionFaultPostContracts.ExpressionReflectsAt ExpressionTraceAt protocol ready
      ExpressionFailurePostContracts.TrivialExpressionPost size model program context evidence source certificate faults := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted trace
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ := meaning certified found environments heaps locals agrees typed initial admitted trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
    maps, worlds, frame, metadata, transition, ExpressionFailurePostContracts.OutcomePost.of_trivial represented⟩

theorem preserves_fault_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ id, id ∈ ids → ∀ size, size < budget →
      ExpressionPreservesAt protocol ready size model program context evidence source
        (fun current expression code => expression = id ∧ certificate current expression code) faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : ready initial)
    {size : Nat}
    (execution : SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, transition, _post⟩ := preserves_fault_bounded_with_post protocol ready
      ExpressionFailurePostContracts.TrivialExpressionPost ExpressionFailurePostContracts.TrivialExpressionsPost
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source) budget tree
      (fun id member size smaller => preserves_child_trivial_post protocol ready (meaning id member size smaller))
      environments heaps locals layout actualTyped initial initialReady execution bounded
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩

theorem reflects_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ id, id ∈ ids → ∀ size, size < budget →
      ExpressionReflectsAt protocol ready size model program context evidence source
        (fun current expression code => expression = id ∧ certificate current expression code) faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : ready initial)
    {size : Nat}
    (evaluated : EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) (bounded : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      TraceAt program sourceSize context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ∀ sources, outcome = .ok sources → ready reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, transition, _post⟩ := reflects_bounded_with_post protocol ready
      ExpressionFailurePostContracts.TrivialExpressionPost ExpressionFailurePostContracts.TrivialExpressionsPost
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source) budget tree
      (fun id member size smaller => reflects_child_trivial_post protocol ready (meaning id member size smaller))
      environments heaps locals layout actualTyped initial initialReady evaluated bounded
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩

theorem preserves_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ id, id ∈ ids → ∀ size, size < budget →
      ExpressionPreservesAt protocol ready size model program context evidence source
        (fun current expression code => expression = id ∧ certificate current expression code) faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : ready initial)
    {size : Nat}
    (execution : TraceAt program size context evidence source environment before ids outcome after) (bounded : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ∀ sources, outcome = .ok sources → ready reached := by
  cases execution with
  | values execution =>
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, transition⟩ := preserves_values_bounded protocol ready budget tree meaning environments heaps locals layout actualTyped initial initialReady execution bounded
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .values represented,
      finalHeaps, maps, worlds, frame, metadata, by obtain ⟨reached, related, finalReady⟩ := transition; exact ⟨reached, related, fun _ _ => finalReady⟩⟩
  | fault execution =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, transition⟩ := preserves_fault_bounded protocol ready budget tree meaning environments heaps locals layout actualTyped initial initialReady execution bounded
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault represented,
      finalHeaps, maps, worlds, frame, metadata, by obtain ⟨reached, related⟩ := transition; exact ⟨reached, related, fun _ impossible => nomatch impossible⟩⟩

end WithReady

variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}

/-- Constant readiness preserves the original actual-state contracts. -/
private theorem true_preserves_at {size : Nat}
    (meaning : ExpressionPreservesAt protocol size model program context evidence source certificate faults) :
    WithReady.ExpressionPreservesAt protocol (fun _ => True) size model program context evidence source certificate faults := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial _ trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
    meaning certified found environments heaps locals agrees typed initial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, fun _ _ => True.intro⟩

private theorem true_reflects_at {size : Nat}
    (meaning : ExpressionReflectsAt protocol size model program context evidence source certificate faults) :
    WithReady.ExpressionReflectsAt protocol (fun _ => True) size model program context evidence source certificate faults := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed initial _ evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
    meaning certified found environments heaps locals agrees typed initial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, fun _ _ => True.intro⟩

theorem preserves_values_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → ExpressionPreservesAt protocol size model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    {size : Nat}
    (execution : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment before ids sources after) (bounded : size ≤ budget) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, _⟩ := WithReady.preserves_values_bounded protocol (fun _ => True) budget tree
        (fun child _ size smaller => by
          intro current expression code certified
          exact true_preserves_at protocol (meaning size smaller) certified.2)
        environments heaps locals layout actualTyped initial True.intro execution bounded
  exact ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩

theorem preserves_fault_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → ExpressionPreservesAt protocol size model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    {size : Nat}
    (execution : SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact WithReady.preserves_fault_bounded protocol (fun _ => True) budget tree
    (fun child _ size smaller => by
          intro current expression code certified
          exact true_preserves_at protocol (meaning size smaller) certified.2)
    environments heaps locals layout actualTyped initial True.intro execution bounded

theorem reflects_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → ExpressionReflectsAt protocol size model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    {size : Nat}
    (evaluated : EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) (bounded : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      TraceAt program sourceSize context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata,
      reached, related, _⟩ := WithReady.reflects_bounded protocol (fun _ => True) budget tree
        (fun child _ size smaller => by
          intro current expression code certified
          exact true_reflects_at protocol (meaning size smaller) certified.2)
        environments heaps locals layout actualTyped initial True.intro evaluated bounded
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, reached, related⟩

theorem preserves_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → ExpressionPreservesAt protocol size model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    {size : Nat}
    (execution : TraceAt program size context evidence source environment before ids outcome after) (bounded : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata,
      reached, related, _⟩ := WithReady.preserves_bounded protocol (fun _ => True) budget tree
        (fun child _ size smaller => by
          intro current expression code certified
          exact true_preserves_at protocol (meaning size smaller) certified.2)
        environments heaps locals layout actualTyped initial True.intro execution bounded
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, reached, related⟩

end Stateful

/-- Legacy entries have a proof-only lifted witness and no record data. -/
private def legacyProtocol (entry : ProtectedExpressionMeaning.Entry) :
    ProtectedStateTransition.Protocol Unit where
  State index := PLift (entry index.scope index.mapping index.world index.heap index.store index.canonical)
  records _ := ()
  Relates _ _ := True
  refl _ := True.intro
  trans _ _ := True.intro

private theorem lift_preserves_at
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry) {size : Nat}
    (meaning : ExpressionPreservesAt size model program context evidence source certificate faults entry) :
    Stateful.ExpressionPreservesAt (legacyProtocol entry) size model program context evidence source certificate faults := by
  intro scope id lowered generated node found mapping world admin environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals agrees typed initial.down trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata,
    ⟨PLift.up (transport.extend initial.down maps worlds frame metadata), True.intro⟩⟩

private theorem lift_reflects_at
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry) {size : Nat}
    (meaning : ExpressionReflectsAt size model program context evidence source certificate faults entry) :
    Stateful.ExpressionReflectsAt (legacyProtocol entry) size model program context evidence source certificate faults := by
  intro scope id lowered generated node found mapping world admin environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals agrees typed initial.down evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata,
    ⟨PLift.up (transport.extend initial.down maps worlds frame metadata), True.intro⟩⟩

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
include transport


omit transport in
private theorem preserves_at_of_unbounded
    (meaning : ProtectedExpressionMeaning.Preserves model program context evidence source certificate faults entry)
    (size : Nat) : ExpressionPreservesAt size model program context evidence source certificate faults entry := by
  intro scope id lowered generated node found mapping world admin environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed installed trace
  exact meaning generated found environments heaps locals agrees typed installed trace.sound

omit transport in
private theorem reflects_at_of_unbounded
    (meaning : ProtectedExpressionMeaning.Reflects model program context evidence source certificate faults entry)
    (size : Nat) : ExpressionReflectsAt size model program context evidence source certificate faults entry := by
  intro scope id lowered generated node found mapping world admin environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed installed evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, rest⟩ := meaning generated found environments heaps locals agrees typed installed evaluated.sound
  obtain ⟨sourceSize, sized⟩ := ExpressionTraceAt.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, rest⟩

theorem preserves_values_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → ExpressionPreservesAt size model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    {size : Nat}
    (execution : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment before ids sources after) (bounded : size ≤ budget) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := Stateful.preserves_values_bounded (legacyProtocol entry) budget tree
      (fun size bounded => lift_preserves_at transport (meaning size bounded))
      environments heaps locals layout actualTyped (PLift.up installedEntry) execution bounded
  exact ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩

theorem preserves_fault_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → ExpressionPreservesAt size model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    {size : Nat}
    (execution : SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := Stateful.preserves_fault_bounded (legacyProtocol entry) budget tree
      (fun size bounded => lift_preserves_at transport (meaning size bounded))
      environments heaps locals layout actualTyped (PLift.up installedEntry) execution bounded
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩

theorem reflects_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → ExpressionReflectsAt size model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    {size : Nat}
    (evaluated : EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) (bounded : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      TraceAt program sourceSize context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := Stateful.reflects_bounded (legacyProtocol entry) budget tree
      (fun size bounded => lift_reflects_at transport (meaning size bounded))
      environments heaps locals layout actualTyped (PLift.up installedEntry) evaluated bounded
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata⟩

theorem preserves_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → ExpressionPreservesAt size model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    {size : Nat}
    (execution : TraceAt program size context evidence source environment before ids outcome after) (bounded : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := Stateful.preserves_bounded (legacyProtocol entry) budget tree
      (fun size bounded => lift_preserves_at transport (meaning size bounded))
      environments heaps locals layout actualTyped (PLift.up installedEntry) execution bounded
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩

theorem preserves_values (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ProtectedExpressionMeaning.Preserves model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    (execution : Dynamic.ExpressionsEvaluate program context evidence source environment before ids sources after) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.ExpressionsEvaluate.has_size execution
  exact preserves_values_bounded transport size tree (fun child _ => preserves_at_of_unbounded meaning child)
    environments heaps locals layout actualTyped installedEntry sized (Nat.le_refl size)


theorem preserves_fault (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ProtectedExpressionMeaning.Preserves model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    (execution : Dynamic.ExpressionsFault program context evidence source environment before ids reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.ExpressionsFault.has_size execution
  exact preserves_fault_bounded transport size tree (fun child _ => preserves_at_of_unbounded meaning child)
    environments heaps locals layout actualTyped installedEntry sized (Nat.le_refl size)


theorem reflects (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ProtectedExpressionMeaning.Reflects model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    reflects_bounded transport (size + 1) tree (fun child _ => reflects_at_of_unbounded meaning child)
      environments heaps locals layout actualTyped installedEntry sized (by omega)
  exact ⟨outcome, after, finalMap, finalWorld, trace.sound, rest⟩


theorem preserves (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ProtectedExpressionMeaning.Preserves model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    (execution : Trace program context evidence source environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := TraceAt.has_size execution
  exact preserves_bounded transport size tree (fun child _ => preserves_at_of_unbounded meaning child)
    environments heaps locals layout actualTyped installedEntry sized (Nat.le_refl size)

end Solcore.SourceSemantics.CoreLowering.ProtectedDataExpressionSequence

-- Protected primitive/control composition.
namespace Solcore.SourceSemantics.CoreLowering.ProtectedExpressionCompositions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives
open CompatibleExpressionConditionals
open CompatibleExpressionTypedCompositions (Head)
private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId) (first second : SourceCoreBasic.LoweredExpr) :
    GenericExpressionMeaning.Certificate := fun current id code =>
  current = scope ∧ ((id = left ∧ code = first) ∨ (id = right ∧ code = second))

private theorem two_tree {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {left right : ExpressionId}
    {leftNode rightNode : ExpressionNode} {first second : SourceCoreBasic.LoweredExpr}
    (leftFound : source.lookupExpression? left = some leftNode)
    (rightFound : source.lookupExpression? right = some rightNode) :
    DataExpressionSequence.Tree source (Two scope left right first second) scope
      [left, right] [leftNode.type, rightNode.type] [first, second] :=
  .cons leftFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩ (.single rightFound ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

private theorem pair_result {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {leftType rightType : TypeSystem.Ty}
    {first second : SourceCoreBasic.LoweredExpr} {faults : FunctionCalls.FaultRep}
    {sequence : DataExpressionSequence.Outcome} {value : Value}
    (result : DataExpressionSequence.Result (CompatibleAmbientHeap.payloadModel checked registry functions)
      mapping world [leftType, rightType] [first, second] faults sequence value) :
    ∃ outcome, CompatibleExpressionProducts.PacksOutcome sequence outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
        mapping world (.product leftType rightType) (.product first.type second.type) faults outcome value := by
  cases result with
  | values represented =>
    change DataExpressionSequence.Values _ _ _ [leftType, rightType] [first.type, second.type] _ _ at represented
    cases represented with
    | cons left tail =>
      cases tail with
      | cons right tail =>
        cases tail
        exact ⟨_, .values (.cons (.singleton _)), .value (.product left right)⟩
  | fault matched => exact ⟨_, .fault _, .fault matched⟩


variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
include transport

theorem Head.preserves
    (unique : NodeOccurrencesUnique source)
    (meaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults entry) :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults entry := by
  intro scope id lowered tree
  cases tree with
  | @group node inner innerNode lowered metadata form innerFound sourceType child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ih innerFound environments heaps locals agrees actualTyped installedEntry (CompatibleExpressionProducts.group_inv metadata form unique trace)
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using represented
  | @pair node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree =>
    have leftIH := @meaning _ _ _ firstTree
    have rightIH := @meaning _ _ _ secondTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have children : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
        program context evidence source (Two scope left right first second) faults entry := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    obtain ⟨sequence, sourceTrace, packed⟩ := CompatibleExpressionProducts.pair_inv metadata form unique trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ProtectedDataExpressionSequence.preserves transport (two_tree (first := first) (second := second) leftFound rightFound) children environments heaps locals agrees actualTyped installedEntry sourceTrace
    obtain ⟨actualOutcome, actualPack, payload⟩ := pair_result represented
    have sameOutcome := actualPack.functional packed
    subst actualOutcome
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using payload

  | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have sourceStep := unary_inv metadata form unique trace
    cases sourceStep with
    | value childTrace applied =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih childFound environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, actualApplied, coreApplied, resultRep⟩ := profile.preserves payload
        have same := actualApplied.functional applied
        subst sourceResult
        refine ⟨.inRight .word result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
        · rw [unary_rename]; exact LocalPrimitiveResults.unary_success evaluated coreApplied
        · exact .value (outputType ▸ resultRep)
    | fault childTrace =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih childFound environments heaps locals agrees actualTyped installedEntry (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [unary_rename]; exact LocalPrimitiveResults.unary_failure evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | invalid childTrace failed =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := ih childFound environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨_, _, applied, _, _⟩ := profile.preserves payload
        exact False.elim (unary_fault_excluded applied failed)
  | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
    have leftIH := @meaning _ _ _ leftTree
    have rightIH := @meaning _ _ _ rightTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have sourceStep := binary_inv metadata form unique trace
    cases sourceStep with
    | leftFault childTrace =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped installedEntry (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact mode.left_failure operator evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | leftInvalid childTrace invalid =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := leftIH leftFound environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        exact False.elim (profile.left_valid payload invalid)
    | short childTrace circuit =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit evaluated
        exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
          .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata⟩
    | rightFault firstTrace continues secondTrace =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped installedEntry (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) (.fault secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact profile.right_failure payload continues first second,
            .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
    | value firstTrace continues secondTrace applied =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped installedEntry (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) (.value secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | value rightPayload =>
          rw [rightType] at rightPayload
          have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
          obtain ⟨sourceResult, result, actualApplied, resultRep, combined⟩ := profile.right_success leftPayload rightPayload continues first second
          have same := actualApplied.functional applied
          subst sourceResult
          exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
            .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
    | invalid firstTrace continues secondTrace failed =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped installedEntry (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, _, _, _, second, represented, _, maps, worlds, _⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) (.value secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | value rightPayload =>
          rw [rightType] at rightPayload
          have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
          obtain ⟨_, _, applied, _, _⟩ := profile.right_success leftPayload rightPayload continues first second
          exact False.elim (binary_fault_excluded applied failed)

  | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
    have conditionIH := @meaning _ _ _ conditionTree
    have thenIH := @meaning _ _ _ thenTree
    have elseIH := @meaning _ _ _ elseTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have sourceStep := conditional_inv metadata form unique trace
    cases sourceStep with
    | fault childTrace =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped installedEntry (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [choose_rename]; exact LocalControl.choose_failure type evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | @branch flag middle outcome after conditionTrace branchTrace =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped installedEntry (.value conditionTrace)
      cases represented with
      | value payload =>
        obtain ⟨actualFlag, sourceEq, coreEq⟩ := bool_fields payload
        cases sourceEq
        subst coreEq
        cases flag with
        | false =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
            elseIH elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
          · rw [choose_rename]; exact LocalControl.choose_false type first branch
          · simpa only [elseType] using represented
        | true =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
            thenIH thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
          · rw [choose_rename]; exact LocalControl.choose_true type first branch
          · simpa only [thenType] using represented
    | invalid childTrace invalid runtimeType =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := conditionIH conditionFound environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨flag, rfl, _⟩ := bool_fields payload
        exact False.elim (invalid trivial)


theorem Head.reflects
    (meaning : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults entry) :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults entry := by
  intro scope id lowered tree
  cases tree with
  | @group node inner innerNode lowered metadata form innerFound sourceType child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ih innerFound environments heaps locals agrees actualTyped installedEntry evaluated
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.group_intro metadata form trace, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using represented
  | @pair node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree =>
    have leftIH := @meaning _ _ _ firstTree
    have rightIH := @meaning _ _ _ secondTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have children : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
        program context evidence source (Two scope left right first second) faults entry := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    obtain ⟨sequence, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ProtectedDataExpressionSequence.reflects transport (two_tree (first := first) (second := second) leftFound rightFound) children environments heaps locals agrees actualTyped installedEntry evaluated
    obtain ⟨outcome, packed, payload⟩ := pair_result represented
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.pair_intro metadata form sourceTrace packed, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using payload

  | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [unary_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih childFound environments heaps locals agrees actualTyped installedEntry childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_failure (operator := core) childEvaluation) complete
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.fault failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih childFound environments heaps locals agrees actualTyped installedEntry childEvaluation
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, applied, coreApplied, resultRep⟩ := profile.preserves payload
        obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_success childEvaluation coreApplied) complete
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.value childTrace applied),
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata⟩
  | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
    have leftIH := @meaning _ _ _ leftTree
    have rightIH := @meaning _ _ _ rightTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [Mode.binary_rename] at evaluated
    have complete := evaluated
    rw [Mode.binary_eq] at evaluated
    cases evaluated with
    | caseLeft leftEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped installedEntry leftEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (mode.left_failure operator leftEvaluation)
          exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.leftFault failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight leftEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped installedEntry leftEvaluation
      cases represented with
      | @value sourceValue coreValue payload =>
        rw [leftType] at payload
        cases trace with
        | value firstTrace =>
          rcases profile.left_progress payload with ⟨output, circuit⟩ | continues
          · obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit leftEvaluation
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
            exact ⟨_, middle, middleMap, middleWorld, binary_intro metadata form (.short firstTrace circuit),
              .value (outputType ▸ resultRep), middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩
          · obtain ⟨rightValue, rightStore, rightEvaluation⟩ := profile.right_evaluated payload continues branch
            have shifted := rightEvaluation
            rw [← GenericExpressionMeaning.rename_prefix] at shifted
            obtain ⟨rightOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
              rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees _)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) shifted
            cases represented with
            | fault matched =>
              cases trace with
              | fault failed =>
                have combined := profile.right_failure payload continues leftEvaluation rightEvaluation
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
                exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.rightFault firstTrace continues failed),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
            | value rightPayload =>
              rw [rightType] at rightPayload
              have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
              obtain ⟨sourceResult, result, applied, resultRep, combined⟩ :=
                profile.right_success leftPayload rightPayload continues leftEvaluation rightEvaluation
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
              cases trace with
              | value secondTrace =>
                exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.value firstTrace continues secondTrace applied),
                  .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata⟩

  | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
    have conditionIH := @meaning _ _ _ conditionTree
    have thenIH := @meaning _ _ _ thenTree
    have elseIH := @meaning _ _ _ elseTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [choose_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped installedEntry childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalControl.choose_failure type childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, conditional_intro metadata form (.fault failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped installedEntry childEvaluation
      cases represented with
      | value payload =>
        obtain ⟨flag, sourceEq, coreEq⟩ := bool_fields payload
        subst sourceEq
        subst coreEq
        cases trace with
        | value conditionTrace =>
          have selected := choose_branch_evaluated branch
          cases flag with
          | false =>
            change Evaluates _ _ ((elseCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
              elseIH elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace branchTrace),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
            simpa only [elseType] using represented
          | true =>
            change Evaluates _ _ ((thenCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
              thenIH thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace branchTrace),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
            simpa only [thenType] using represented


end Solcore.SourceSemantics.CoreLowering.ProtectedExpressionCompositions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateCellAllocation
/-! Protected allocation accepts genuine ordinary or generalized Source steps.
Its actual reached state, captures and full observation are retained by the
same protocol used for ordinary calls. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.CellAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion
universe u v
variable {Records : Type v} {catalog : SourceCoreDataCatalog.Catalog} {nativeDefinitions : DataEnvironment}

structure Producer (protocol : Protocol.{u, v} Records)
    (layouts : SourceCoreAllocationLayouts.Prepared) (layout : SourceCoreCallableIndexedFrames.Layout)
    (model : GenericHeap.CellModel nativeDefinitions) where
  Ready : {index : Index} → protocol.State index → Location → NativeFrame → Prop
  complete : ∀ {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (_same : annotation.original = allocation.expression)
    (_definitions : layouts.definitions = nativeDefinitions) (_registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {contextLocation : Location} {native : NativeFrame}
    {sourceCell : Dynamic.Cell} {payload : Option Value} {sourceLocation : Dynamic.Location}
    (_environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope environment canonical nativeDefinitions)
    (_agrees : EnvironmentsAgree request.references canonical actual)
    (_heaps : GenericHeap.CellHeapRepresents model mapping world before store)
    (_reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (_payloadAt : PayloadAt request actual payload)
    (_cell : model.Represents mapping world sourceCell (optionalValue request.payloadType payload) request.payloadType)
    (_allocated : CallableIndexedCellAllocation.SourceStep before sourceCell sourceLocation after)
    (initial : protocol.State ⟨request.scope, mapping, world, before, store, canonical⟩)
    (_ready : Ready initial contextLocation native),
    ∃ captured,
      Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope) nativeDefinitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      GenericHeap.CellHeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved mapping store (mapping ++ [store.length + 2])
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      Transition protocol initial
        ⟨(request.binder.id, request.payloadType) :: request.scope, mapping ++ [store.length + 2],
          world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType], after,
          store ++ [SourceCoreCallableIndexedFrames.encode layout native,
            SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload],
          .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical⟩

/-- The compatibility producer observes the actual proved administrative effects.
It preserves the complete input record observation and adds no snapshot record. -/
def of_administrative (protocol : Protocol.{u, v} Records)
    (transport : AdministrativeTransport protocol) (bindings : Bindings protocol)
    (layouts : SourceCoreAllocationLayouts.Prepared) (layout : SourceCoreCallableIndexedFrames.Layout)
    (model : GenericHeap.CellModel nativeDefinitions) : Producer (catalog := catalog) protocol layouts layout model where
  Ready _ _ _ := True
  complete := by
    intro owner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceCell payload sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial _ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame⟩ :=
      CallableIndexedCellAllocation.preserves_with_captures allocation annotation same definitions registered
        environments agrees heaps reference read payloadAt cell allocated
    let extended := transport.extend initial
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
      (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType]) from ⟨_, rfl⟩)
      frame allocated.metadata
    refine ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      bindings.prepend extended request.binder.id request.payloadType
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)), ?_⟩
    exact protocol.trans
      (transport.related initial _ _ frame allocated.metadata)
      (bindings.prepend_related extended _ _ _)

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.CellAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateScopeReturn
/-! A lexical prefix returns the actual reached state to its input scope and
canonical environment. The receipt applies after any later heap/store effects
and keeps the complete record observation. Its constructors use only the
identity operation and the proved concrete binder restoration interface. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
open Core Frontend SourceInference
universe u v

structure ReturnTo {Records : Type v} (protocol : Protocol.{u, v} Records)
    (scope : SourceCoreLocalCell.Scope) (canonical : Environment)
    (reachedScope : SourceCoreLocalCell.Scope) (reachedCanonical : Environment) where
  restore : ∀ {mapping world heap store},
    protocol.State ⟨reachedScope, mapping, world, heap, store, reachedCanonical⟩ →
    protocol.State ⟨scope, mapping, world, heap, store, canonical⟩
  related : ∀ {mapping world heap store}
    (reached : protocol.State ⟨reachedScope, mapping, world, heap, store, reachedCanonical⟩),
    protocol.Relates reached (restore reached)
  records_eq : ∀ {mapping world heap store}
    (reached : protocol.State ⟨reachedScope, mapping, world, heap, store, reachedCanonical⟩),
    protocol.records (restore reached) = protocol.records reached

variable {Records : Type v} {protocol : Protocol.{u, v} Records}
  {scope middleScope reachedScope : SourceCoreLocalCell.Scope}
  {canonical middleCanonical reachedCanonical : Environment}

def ReturnTo.refl (protocol : Protocol.{u, v} Records) (scope : SourceCoreLocalCell.Scope)
    (canonical : Environment) : ReturnTo protocol scope canonical scope canonical where
  restore reached := reached
  related reached := protocol.refl reached
  records_eq _ := rfl

/-- Compose concrete scope restoration without changing the actual effects. -/
def ReturnTo.then (first : ReturnTo protocol scope canonical middleScope middleCanonical)
    (last : ReturnTo protocol middleScope middleCanonical reachedScope reachedCanonical) :
    ReturnTo protocol scope canonical reachedScope reachedCanonical where
  restore reached := first.restore (last.restore reached)
  related reached := protocol.trans (last.related reached) (first.related (last.restore reached))
  records_eq reached := (first.records_eq (last.restore reached)).trans (last.records_eq reached)

/-- Remove one real source binder from any later reached state. -/
def ReturnTo.binding (bindings : Bindings protocol) (scope : SourceCoreLocalCell.Scope)
    (canonical : Environment) (id : Resolved.LocalId) (type : Ty) (value : Value) :
    ReturnTo protocol scope canonical ((id, type) :: scope) (value :: canonical) where
  restore := fun {mapping world heap store} reached =>
    bindings.restore (index := ⟨scope, mapping, world, heap, store, canonical⟩)
      (id := id) (type := type) (value := value) reached
  related := fun {mapping world heap store} reached =>
    bindings.restore_related (index := ⟨scope, mapping, world, heap, store, canonical⟩)
      (id := id) (type := type) (value := value) reached
  records_eq := fun {mapping world heap store} reached =>
    bindings.restore_records (index := ⟨scope, mapping, world, heap, store, canonical⟩)
      (id := id) (type := type) (value := value) reached

theorem ReturnTo.transition (receipt : ReturnTo protocol scope canonical reachedScope reachedCanonical)
    {mapping world heap store}
    (reached : protocol.State ⟨reachedScope, mapping, world, heap, store, reachedCanonical⟩) :
    Transition protocol reached ⟨scope, mapping, world, heap, store, canonical⟩ :=
  ⟨receipt.restore reached, receipt.related reached⟩


end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchPrefix
/-! Match prefixes use a real marked allocation producer and retain a future
scope restoration receipt. Compatibility wrappers have a constant observation;
they forget the added witness after executing the same prefix proof. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.MatchPrefix
open Core Frontend SourceInference

/-- Restore the constant witness used by the original unguarded APIs. -/
def unitBindings : Bindings OrdinaryAllocation.unitProtocol where
  prepend _ _ _ _ := ()
  prepend_related _ _ _ _ := True.intro
  prepend_records _ _ _ _ := rfl
  restore _ := ()
  restore_related _ := True.intro
  restore_records _ := rfl

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.MatchPrefix
end
