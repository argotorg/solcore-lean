import Solcore.SourceSemantics.CoreLowering.ProtectedStateBindings
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOrdinaryAllocation

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

private def unitTransport : AdministrativeTransport unitProtocol where
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

def unitProducer (layouts : SourceCoreAllocationLayouts.Prepared) (layout : SourceCoreCallableIndexedFrames.Layout)
    (model : GenericHeap.PayloadModel catalog projects nativeDefinitions) : Producer unitProtocol layouts layout model :=
  of_administrative unitProtocol unitTransport unitBindings layouts layout model

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.OrdinaryAllocation
