import Solcore.SourceSemantics.CoreLowering.ProtectedStateBindings
import Solcore.SourceSemantics.CoreLowering.CallableIndexedCellAllocation

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
