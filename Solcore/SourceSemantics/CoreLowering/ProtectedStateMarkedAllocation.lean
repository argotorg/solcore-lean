import Solcore.SourceSemantics.CoreLowering.ProtectedStateOrdinaryAllocation

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
