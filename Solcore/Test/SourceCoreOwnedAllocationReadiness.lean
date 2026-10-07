import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness

/-! Formal consumers of actual allocation readiness and the same registered
post-pool through lexical binder removal. The reached ghost is projected from
the actual pool; the stable origin seed is never substituted for it. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreOwnedAllocationReadiness
open Core Frontend SourceInference
open Solcore.SourceSemantics
open Solcore.SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedAllocationProducer

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)

include model in
theorem ready_acquires_the_reached_rows_ghost {index : ProtectedStateTransition.Index}
    (reached : State headers keys index) {location : Location} {native : NativeFrame}
    (seed : StableOwner keys location native)
    (read : index.store.read? location = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native)) :
    ∃ selected : Fin keys.length, ∃ metadata,
      keys[selected.val].frameLocation = location ∧
      (reached.rows selected).authority.current = native ∧
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        native (reached.rows selected).authority.ghost metadata := by
  obtain ⟨selected, metadata, physicalOwner, current, carried⟩ :=
    readyAt_of_stableOwner model seed reached read
  refine ⟨selected, metadata, physicalOwner, current, ?_⟩
  simpa only [current] using carried

theorem retained_actual_read_supplies_next_allocation {initial reached : ProtectedStateTransition.Index}
    (state : State headers keys reached) {location : Location} {native : NativeFrame}
    (seed : StableOwner keys location native)
    (read : initial.store.read? location = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : location ∉ initial.mapping)
    (preserved : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    (producer headers keys model).Ready state location native :=
  ProtectedStateTransition.OrdinaryAllocation.ReadyAt.after_administrative
    (readyAt_of_stableOwner model seed) state read unmapped preserved

theorem transient_view_cannot_produce_a_stable_snapshot {index : ProtectedStateTransition.Index}
    (state : State headers keys index) (location : Location) (id target : Word) (caller : Int) :
    ¬ (producer headers keys model).Ready state location (.view id target caller) :=
  not_ready_view state location id target caller

theorem transient_view_is_not_a_body_seed (location : Location) (id target : Word) (caller : Int) :
    ¬ StableOwner keys location (.view id target caller) := by
  intro seed
  obtain ⟨selected, ghost, metadata, _physicalOwner, carried⟩ := seed
  cases carried

section CompletedAllocation
variable {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {request : SourceCoreSourceCells.Request} {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
  (allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts owner active request)
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame globals allocate request)
  (same : annotation.original = allocation.expression)
  (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {before after : Dynamic.Heap} {store : Store}
  (initial : State headers keys ⟨request.scope, mapping, world, before, store, canonical⟩)
  (selected : Fin keys.length) {metadata : Option MetadataState}
  (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (initial.rows selected).authority.current (initial.rows selected).authority.ghost metadata)
  {payload : Option Value} {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree request.references canonical actual)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type keys[selected.val].frameLocation))
  (payloadAt : CallableIndexedAllocationCompletion.PayloadAt request actual payload)
  (cell : GenericHeap.CellRepresents model mapping world
    ⟨request.binder.scheme.body, sourceValue, none⟩
    (CallableIndexedAllocationCompletion.optionalValue request.payloadType payload) request.payloadType)
  (allocated : Dynamic.Heap.Allocates before request.binder.scheme.body sourceValue sourceLocation after)

include same registered history environments agrees heaps reference payloadAt cell allocated in
/-- The real owned completion supplies one post-witness for the generic
bound transition and the exact append receipt. Binder restoration consumes
that same post-witness and retains every ordered row's complete list. -/
theorem actual_completion_restores_the_registered_post :
    ∃ captured,
      CallableIndexedAllocationCompletion.Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope) compiled.indexed.layouts.definitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      ∃ final : State headers keys
        ⟨(request.binder.id, request.payloadType) :: request.scope, mapping ++ [store.length + 2],
          world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType], after,
          store ++ [SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
            SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
            CallableIndexedAllocationCompletion.optionalValue request.payloadType payload],
          .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical⟩,
        Relates initial final ∧
        records final selected = records initial selected ++
          [⟨store.length, (initial.rows selected).authority.current, (initial.rows selected).authority.ghost, metadata⟩] ∧
        (∀ i, i ≠ selected → records final i = records initial i) ∧
        records ((CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore
          (index := ⟨request.scope, mapping ++ [store.length + 2],
            world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType], after,
            store ++ [SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
              SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
              CallableIndexedAllocationCompletion.optionalValue request.payloadType payload], canonical⟩)
          (id := request.binder.id) (type := request.payloadType)
          (value := .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)) final) = records final ∧
        ProtectedStateTransition.Transition (protocol headers keys) initial
          ⟨request.scope, mapping ++ [store.length + 2],
            world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType], after,
            store ++ [SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
              SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
              CallableIndexedAllocationCompletion.optionalValue request.payloadType payload], canonical⟩ := by
  obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, _reference, _boundEnvironment, _frame,
    final, related, selectedRecords, otherRecords⟩ :=
    CallableIndexedOwnedOrdinaryAllocation.completed_bind allocation annotation same registered initial selected
      history environments agrees heaps reference payloadAt cell allocated
  refine ⟨captured, captures, capturedTyped, evaluated, finalHeaps, final, related, selectedRecords, otherRecords, rfl, ?_⟩
  exact ProtectedStateTransition.Bindings.restore_reached
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys) initial ⟨final, related⟩

end CompletedAllocation
end Solcore.Test.SourceCoreOwnedAllocationReadiness
