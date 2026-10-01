import Solcore.SourceSemantics.CoreLowering.CallableIndexedCaptureEnvironment
import Solcore.SourceSemantics.CoreLowering.GenericHeap

/-! Actual marked ordinary allocation in the common heap relation. The native
snapshot and marker extend only the typing world; the optional payload alone
extends the source-location map. The payload model must use the real complete
definition table, including administrative definitions. This does not lift an
existing smaller catalog automatically or represent generalized principal cells.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOrdinaryAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion

private theorem scope_reference {catalog : SourceCoreDataCatalog.Catalog} {nativeDefinitions : DataEnvironment} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical nativeDefinitions)
    {index : Nat} {binding : Resolved.LocalId × Ty} (found : scope[index]? = some binding) :
    ∃ target, canonical[index]? = some (.cellRef (OptionalCell.cellType binding.2) target) ∧
      world[target]? = some (OptionalCell.cellType binding.2) := by
  induction related generalizing index with
  | nil => simp at found
  | @cons scope source canonical id location target payload reference tail ih =>
    cases index with
    | zero =>
      have same : (id, payload) = binding := Option.some.inj found
      subst binding
      exact ⟨target, rfl, reference.typed⟩
    | succ index => exact ih found
  | @internal scope source canonical id location target payload reference absent tail ih =>
    cases index with
    | zero =>
      have same : (id, payload) = binding := Option.some.inj found
      subst binding
      exact ⟨target, rfl, reference.typed⟩
    | succ index => exact ih found

/-- Capture values and their types follow from the mapped lexical slots, not
from a supplied capture evaluation or an inspection of referenced payloads. -/
theorem captures_typed {catalog : SourceCoreDataCatalog.Catalog} {nativeDefinitions : DataEnvironment} {mapping : LocationMap}
    {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {canonical actual : Environment} {references : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical nativeDefinitions)
    (agrees : EnvironmentsAgree references canonical actual) :
    ∃ captured, Captures actual references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope) nativeDefinitions := by
  have slots : ∀ index binding, scope[index]? = some binding → ∃ target,
      actual[references index]? = some (.cellRef (OptionalCell.cellType binding.2) target) ∧
      world[target]? = some (OptionalCell.cellType binding.2) := by
    intro index binding found
    obtain ⟨target, selected, typed⟩ := scope_reference related found
    exact ⟨target, agrees selected, typed⟩
  clear related agrees canonical source administrative mapping
  induction scope generalizing references with
  | nil => exact ⟨.unit, .nil, .unit⟩
  | cons binding rest ih =>
    obtain ⟨id, type⟩ := binding
    obtain ⟨target, selected, typed⟩ := slots 0 (id, type) rfl
    cases rest with
    | nil => exact ⟨_, .singleton selected, .cellRef typed⟩
    | cons next tail =>
      obtain ⟨captured, selectedTail, typedTail⟩ := ih (references := fun index => references (index + 1)) (by
        intro index binding found
        exact slots (index + 1) binding (by simpa using found))
      exact ⟨_, .cons selected selectedTail, .pair (.cellRef typed) typedTail⟩

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}

/-- Two ordinary administrative allocations precede the independently
specified source allocation. World/map extensions use exact actual indices. -/
theorem heap_allocate {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {sourceType : TypeSystem.Ty}
    {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}
    {snapshot marker payload : Value} {snapshotType markerType payloadType : Ty}
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType nativeDefinitions)
    (markerTyped : RuntimeValueHasType world marker markerType nativeDefinitions)
    (cell : GenericHeap.CellRepresents model mapping world
      ⟨sourceType, sourceValue, none⟩ payload payloadType)
    (allocated : Dynamic.Heap.Allocates before sourceType sourceValue sourceLocation after) :
    GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
      after (store ++ [snapshot, marker, payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
        sourceLocation (store.length + 2) payloadType := by
  have snapshotHeaps := heaps.allocate_administrative snapshotTyped
  have markerHeaps := snapshotHeaps.allocate_administrative (markerTyped.weaken (show WorldExtends world (world ++ [snapshotType]) from ⟨_, rfl⟩))
  have cells := cell.extend (LocationMap.Extends.refl mapping)
    (show WorldExtends world ((world ++ [snapshotType]) ++ [markerType]) from ⟨[snapshotType, markerType], by simp⟩)
  simpa [Store.allocate, List.append_assoc, Nat.add_assoc] using markerHeaps.allocate cells allocated

/-- The exact callback receipts, actual lexical environment and independent
ordinary source allocation imply the whole native execution and heap relation.
The source cell keeps its raw declaration type and has no generalized metadata. -/
theorem preserves {layouts : SourceCoreAllocationLayouts.Prepared}
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
    {payload : Option Value} {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope environment canonical nativeDefinitions)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (payloadAt : PayloadAt request actual payload)
    (cell : GenericHeap.CellRepresents model mapping world
      ⟨request.binder.scheme.body, sourceValue, none⟩ (optionalValue request.payloadType payload) request.payloadType)
    (allocated : Dynamic.Heap.Allocates before request.binder.scheme.body sourceValue sourceLocation after) :
    ∃ captured,
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
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) := by
  obtain ⟨captured, selected, typed⟩ := captures_typed environments agrees
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
  exact ⟨captured, evaluates allocation annotation same reference read selected payloadAt,
    afterHeaps, afterReference, allocation_frame _ _ _ _ _⟩

/-- The returned payload reference extends the lexical relation in the usual
source order; the two administrative references never become source binders. -/
theorem bind_environment {mapping : LocationMap} {world : StoreTyping}
    {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Environment} {store : Store}
    {sourceLocation : Dynamic.Location} {id : Resolved.LocalId}
    {snapshotType markerType payloadType : Ty}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (reference : ReferenceRepresents (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
      sourceLocation (store.length + 2) payloadType) :
    DataHeap.EnvRepresents catalog (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType]) administrative
      ((id, payloadType) :: scope) ((id, sourceLocation) :: environment)
      (.cellRef (OptionalCell.cellType payloadType) (store.length + 2) :: canonical) nativeDefinitions :=
  .cons reference (environments.extend ⟨_, rfl⟩ ⟨_, rfl⟩)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOrdinaryAllocation
