import Solcore.SourceSemantics.CoreLowering.GenericCellHeapOperations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOrdinaryAllocation

/-! The emitted snapshot, marker and payload allocations share one proof for
ordinary cells and generalized descriptors. Only the payload allocation extends
the Source location map; both administrative cells retain their actual values. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedCellAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion

inductive SourceStep : Dynamic.Heap → Dynamic.Cell → Dynamic.Location → Dynamic.Heap → Prop where
  | ordinary {before after : Dynamic.Heap} {type : TypeSystem.Ty}
      {value : Option Dynamic.Value} {location : Dynamic.Location}
      (allocated : Dynamic.Heap.Allocates before type value location after) :
      SourceStep before ⟨type, value, none⟩ location after
  | generalized {before after : Dynamic.Heap} {function : Dynamic.GeneralizedClosure}
      {location : Dynamic.Location}
      (allocated : Dynamic.Heap.AllocatesGeneralized before function location after) :
      SourceStep before ⟨function.binder.scheme.body, none, some function⟩ location after

theorem SourceStep.metadata {before after : Dynamic.Heap} {cell : Dynamic.Cell}
    {location : Dynamic.Location} (step : SourceStep before cell location after) :
    Dynamic.HeapMetadataExtend before after := by
  cases step with
  | ordinary allocated => exact .of_allocation allocated
  | generalized allocated => exact .of_generalized_allocation allocated

variable {catalog : SourceCoreDataCatalog.Catalog} {nativeDefinitions : DataEnvironment}
  {model : GenericHeap.CellModel nativeDefinitions}

/-- Exact native indices are shared by both genuine Source allocation rules. -/
theorem heap_allocate {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {sourceCell : Dynamic.Cell}
    {sourceLocation : Dynamic.Location} {snapshot marker payload : Value}
    {snapshotType markerType payloadType : Ty}
    (heaps : GenericHeap.CellHeapRepresents model mapping world before store)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType nativeDefinitions)
    (markerTyped : RuntimeValueHasType world marker markerType nativeDefinitions)
    (cell : model.Represents mapping world sourceCell payload payloadType)
    (allocated : SourceStep before sourceCell sourceLocation after) :
    GenericHeap.CellHeapRepresents model (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
      after (store ++ [snapshot, marker, payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
        sourceLocation (store.length + 2) payloadType := by
  have snapshotHeaps := heaps.allocate_administrative snapshotTyped
  have markerHeaps := snapshotHeaps.allocate_administrative
    (markerTyped.weaken (show WorldExtends world (world ++ [snapshotType]) from ⟨_, rfl⟩))
  have represented := model.extend cell (LocationMap.Extends.refl mapping)
    (show WorldExtends world ((world ++ [snapshotType]) ++ [markerType]) from
      ⟨[snapshotType, markerType], by simp⟩)
  cases allocated with
  | ordinary allocated =>
      simpa [Store.allocate, List.append_assoc, Nat.add_assoc] using
        markerHeaps.allocate_ordinary represented allocated
  | generalized allocated =>
      simpa [Store.allocate, List.append_assoc, Nat.add_assoc] using
        markerHeaps.allocate_generalized represented allocated

/-- Actual allocator receipts and mapped capture slots supply the full emitted
execution; the Source allocation decides the kind of the newly stored cell. -/
theorem preserves_with_captures {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {layout : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (definitions : layouts.definitions = nativeDefinitions)
    (frameRegistered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {contextLocation : Location} {native : NativeFrame}
    {sourceCell : Dynamic.Cell} {payload : Option Value} {sourceLocation : Dynamic.Location}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope environment canonical nativeDefinitions)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : GenericHeap.CellHeapRepresents model mapping world before store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (payloadAt : PayloadAt request actual payload)
    (cell : model.Represents mapping world sourceCell (optionalValue request.payloadType payload) request.payloadType)
    (allocated : SourceStep before sourceCell sourceLocation after) :
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
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) := by
  obtain ⟨captured, selected, typed⟩ := CallableIndexedOrdinaryAllocation.captures_typed environments agrees
  have captureType : allocation.entry.layout.captureType = SourceCoreSourceCells.captureType request.scope := by
    change SourceCoreSourceCells.captureType allocation.entry.key.scope = SourceCoreSourceCells.captureType request.scope
    rw [allocation.keyExact]
    rfl
  have markerRegistered : allocation.entry.layout.Registered nativeDefinitions := definitions ▸ allocation.registered
  have markerTyped : RuntimeValueHasType world (SourceCoreHeapMarkers.markerValue allocation.entry.layout captured)
      allocation.entry.layout.type nativeDefinitions :=
    .constructed markerRegistered.payloadLookup (captureType.symm ▸ typed)
  obtain ⟨afterHeaps, afterReference⟩ := heap_allocate heaps
    (SourceCoreCallableIndexedFrames.encode_runtime_typed world frameRegistered native) markerTyped cell allocated
  exact ⟨captured, selected, typed, evaluates allocation annotation same reference read selected payloadAt,
    afterHeaps, afterReference, allocation_frame _ _ _ _ _⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedCellAllocation
