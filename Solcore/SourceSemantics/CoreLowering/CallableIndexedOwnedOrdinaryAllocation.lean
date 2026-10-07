import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOrdinaryAllocation
import Solcore.SourceSemantics.CoreLowering.ProtectedStateBindings

/-! Ordinary source allocation produces the actual heap correspondence and
registered catalogue post-state together. The payload alone becomes a source
binder. Its preceding snapshot is appended to the selected ordered row, and
lexical restoration retains that reached row's complete record list. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames CallableIndexedAuthorityPool
open CallableIndexedOwnedFunctionState

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- The pool is indexed by the actual heap and store. Canonical lexical
binders change neither its physical cells nor its ordered records. -/
def bindings (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)) :
    ProtectedStateTransition.Bindings (protocol headers keys) where
  prepend state _ _ _ := state
  prepend_related state _ _ _ := Relates.refl state
  prepend_records _ _ _ _ := rfl
  restore state := state
  restore_related state := Relates.refl state
  restore_records _ := rfl

section Allocation
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {request : SourceCoreSourceCells.Request} {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
  (allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts owner active request)
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame globals allocate request)
  (same : annotation.original = allocation.expression)
  (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {sourceEnvironment : Dynamic.Environment} {canonical actual : Environment}
  {before after : Dynamic.Heap} {store : Store}
  (initial : State headers keys ⟨request.scope, mapping, world, before, store, canonical⟩)
  (selected : Fin keys.length) {metadata : Option MetadataState}
  (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (initial.rows selected).authority.current (initial.rows selected).authority.ghost metadata)
  {payload : Option Value} {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope
    sourceEnvironment canonical compiled.indexed.layouts.definitions)
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
/-- One actual allocation producer supplies capture selection, execution,
source/native heap correspondence and the live pool's registered snapshot.
No evaluation, new-record separation or post-state law is assumed. -/
theorem completed_bind :
    ∃ captured,
      CallableIndexedAllocationCompletion.Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope)
        compiled.indexed.layouts.definitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
          OptionalCell.cellType request.payloadType]) after
        (store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
          OptionalCell.cellType request.payloadType]) sourceLocation (store.length + 2) request.payloadType ∧
      DataHeap.EnvRepresents catalog (mapping ++ [store.length + 2])
        (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
          OptionalCell.cellType request.payloadType]) administrative
        ((request.binder.id, request.payloadType) :: request.scope)
        ((request.binder.id, sourceLocation) :: sourceEnvironment)
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical)
        compiled.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store (mapping ++ [store.length + 2])
        (store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      ∃ final : State headers keys
          ⟨(request.binder.id, request.payloadType) :: request.scope, mapping ++ [store.length + 2],
            world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
              OptionalCell.cellType request.payloadType], after,
            store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
              SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
              CallableIndexedAllocationCompletion.optionalValue request.payloadType payload],
            .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical⟩,
        Relates initial final ∧
        records final selected = records initial selected ++
          [⟨store.length, (initial.rows selected).authority.current, (initial.rows selected).authority.ghost, metadata⟩] ∧
        (∀ i, i ≠ selected → records final i = records initial i) := by
  have read := CallableIndexedOwnedFunctionEntries.reached_frame_read initial selected
  obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, mapped, frame⟩ :=
    CallableIndexedOrdinaryAllocation.preserves_with_captures allocation annotation same rfl registered
      environments agrees heaps reference read payloadAt cell allocated
  have bound : ∀ target ∈ mapping, target < store.length := by
    intro target member
    obtain ⟨position, found⟩ := List.mem_iff_getElem?.mp member
    exact heaps.target_lt found
  let record : CallableIndexedSnapshots.Record :=
    ⟨store.length, (initial.rows selected).authority.current, (initial.rows selected).authority.ghost, metadata⟩
  have holds := CallableIndexedSnapshots.completed (layout := compiled.indexed.ancestry.layout.frame) history bound
    (SourceCoreHeapMarkers.markerValue allocation.entry.layout captured)
    (CallableIndexedAllocationCompletion.optionalValue request.payloadType payload)
  have separate : ∀ i : Fin keys.length, record.location ≠ keys[i.val].frameLocation := by
    intro i
    have earlier := (List.getElem?_eq_some_iff.mp (initial.rows i).authority.frame.read).1
    rw [(initial.rows i).frame_eq] at earlier
    exact Nat.ne_of_gt earlier
  let extended := initial.extend (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
    (show WorldExtends world (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
      OptionalCell.cellType request.payloadType]) from ⟨_, rfl⟩)
    frame (Dynamic.HeapMetadataExtend.of_allocation allocated)
  let final := extended.record_snapshot selected record holds separate
  refine ⟨captured, captures, capturedTyped, evaluated, finalHeaps, mapped,
    CallableIndexedOrdinaryAllocation.bind_environment environments mapped, frame, final, ?_, ?_, ?_⟩
  · intro i
    by_cases chosen : i = selected
    · subst i
      exact ⟨[record], Pool.record_snapshot_selected extended selected record holds separate⟩
    · refine ⟨[], ?_⟩
      rw [List.append_nil]
      exact Pool.record_snapshot_other extended selected record holds separate i chosen
  · exact Pool.record_snapshot_selected extended selected record holds separate
  · intro i different
    exact Pool.record_snapshot_other extended selected record holds separate i different

end Allocation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryAllocation
