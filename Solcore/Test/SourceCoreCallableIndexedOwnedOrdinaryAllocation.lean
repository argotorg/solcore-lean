import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryAllocation

/-! The actual ordinary source allocation registers one snapshot and binds
only its payload reference. Removing that source binder consumes the reached
pool and retains its full ordered row histories in the same heap and store. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedOwnedOrdinaryAllocation
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {request : SourceCoreSourceCells.Request} {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {sourceEnvironment : Dynamic.Environment} {canonical actual : Environment}
  {before after : Dynamic.Heap} {store : Store} {metadata : Option MetadataState}
  {payload : Option Value} {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}

/-- Real allocator and source-allocation receipts supply the execution and
post-state. The fresh record remains registered after lexical restoration;
another row sharing the physical frame retains its own distinct history list.
The arbitrary original heap model and all old ordered occurrences survive. -/
theorem actual_bind_then_remove_source_binder
    (allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame
      globals allocate request)
    (same : annotation.original = allocation.expression)
    (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
    (initial : State headers keys ⟨request.scope, mapping, world, before, store, canonical⟩)
    (selected duplicate : Fin keys.length) (differentRow : duplicate ≠ selected)
    (sharedFrame : keys[duplicate.val].frameLocation = keys[selected.val].frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows selected).authority.current (initial.rows selected).authority.ghost metadata)
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
    (allocated : Dynamic.Heap.Allocates before request.binder.scheme.body sourceValue sourceLocation after) :
    ∃ captured,
      let reachedIndex : ProtectedStateTransition.Index :=
        ⟨request.scope, mapping ++ [store.length + 2],
          world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
            OptionalCell.cellType request.payloadType], after,
          store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
            SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
            CallableIndexedAllocationCompletion.optionalValue request.payloadType payload], canonical⟩
      let payloadReference := Value.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)
      let fresh : CallableIndexedSnapshots.Record :=
        ⟨store.length, (initial.rows selected).authority.current, (initial.rows selected).authority.ghost, metadata⟩
      CallableIndexedAllocationCompletion.Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope)
        compiled.indexed.layouts.definitions ∧
      Evaluates actual store annotation.expression payloadReference reachedIndex.store ∧
      GenericHeap.HeapRepresents model reachedIndex.mapping reachedIndex.world reachedIndex.heap reachedIndex.store ∧
      ReferenceRepresents reachedIndex.mapping reachedIndex.world sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved mapping store reachedIndex.mapping reachedIndex.store ∧
      ∃ bound : State headers keys (reachedIndex.prepend request.binder.id request.payloadType payloadReference),
        Relates initial bound ∧
        let final : State headers keys reachedIndex :=
          (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore (index := reachedIndex) (id := request.binder.id) (type := request.payloadType)
            (value := .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)) bound
        Relates initial final ∧ records final = records bound ∧
        DataHeap.EnvRepresents catalog reachedIndex.mapping reachedIndex.world administrative
          request.scope sourceEnvironment canonical compiled.indexed.layouts.definitions ∧
        records final selected = records initial selected ++ [fresh] ∧
        (records final selected).take (records initial selected).length = records initial selected ∧
        (∀ i, i ≠ selected → records final i = records initial i) ∧
        (final.rows duplicate).authority.frameLocation = (final.rows selected).authority.frameLocation ∧
        records final selected ≠ records final duplicate ∧
        ¬ CallableIndexedAuthorityPool.Pool.Registered initial fresh ∧
        fresh ∈ records final selected ∧
        CallableIndexedAuthorityPool.Pool.Registered final fresh ∧
        CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame reachedIndex.mapping reachedIndex.store fresh ∧
        fresh.location ∉ reachedIndex.mapping ∧
        (∀ i : Fin keys.length, fresh.location ≠ keys[i.val].frameLocation) ∧
        (∀ i record, record ∈ records initial i →
          CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
            compiled.indexed.ancestry.layout.frame reachedIndex.mapping reachedIndex.store record) ∧
        ProtectedStateTransition.Transition (protocol headers keys) initial reachedIndex := by
  obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, mapped, _boundEnvironments, frame,
      bound, boundRelated, appended, unchanged⟩ :=
    CallableIndexedOwnedOrdinaryAllocation.completed_bind allocation annotation same registered initial selected
      history environments agrees heaps reference payloadAt cell allocated
  refine ⟨captured, ?_⟩
  dsimp only
  let reachedIndex : ProtectedStateTransition.Index :=
    ⟨request.scope, mapping ++ [store.length + 2],
      world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType request.payloadType], after,
      store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
        CallableIndexedAllocationCompletion.optionalValue request.payloadType payload], canonical⟩
  let fresh : CallableIndexedSnapshots.Record :=
    ⟨store.length, (initial.rows selected).authority.current, (initial.rows selected).authority.ghost, metadata⟩
  let final : State headers keys reachedIndex :=
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore (index := reachedIndex) (id := request.binder.id) (type := request.payloadType)
            (value := .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)) bound
  have finalRecords : records final = records bound :=
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore_records (index := reachedIndex) (id := request.binder.id) (type := request.payloadType)
      (value := .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)) bound
  have finalRelated : Relates initial final := Relates.trans boundRelated
    ((CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore_related (index := reachedIndex) (id := request.binder.id) (type := request.payloadType)
      (value := .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)) bound)
  have selectedAppend : records final selected = records initial selected ++ [fresh] := by
    rw [finalRecords]
    exact appended
  have freshMember : fresh ∈ records final selected := by
    rw [selectedAppend]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have freshOriginallyAbsent : ¬ CallableIndexedAuthorityPool.Pool.Registered initial fresh := by
    rintro ⟨row, member⟩
    exact fresh_record_absent initial row rfl member
  have duplicateUnchanged : records final duplicate = records initial duplicate := by
    rw [finalRecords]
    exact unchanged duplicate differentRow
  have freshHolds := record_snapshot final selected freshMember
  refine ⟨captures, capturedTyped, evaluated, finalHeaps, mapped, frame, bound, boundRelated,
    finalRelated, finalRecords, environments.extend ⟨_, rfl⟩ ⟨_, rfl⟩, selectedAppend, ?_, ?_, ?_, ?_,
    freshOriginallyAbsent, freshMember, ⟨selected, freshMember⟩, freshHolds, freshHolds.administrative, ?_, ?_, ?_⟩
  · rw [selectedAppend]
    simp
  · intro row different
    rw [finalRecords]
    exact unchanged row different
  · exact (final.rows duplicate).frame_eq.trans (sharedFrame.trans (final.rows selected).frame_eq.symm)
  · intro equal
    have member : fresh ∈ records initial duplicate := by
      rw [← duplicateUnchanged, ← equal]
      exact freshMember
    exact freshOriginallyAbsent ⟨duplicate, member⟩
  · intro row
    exact final.separated selected row fresh freshMember
  · intro row record member
    exact record_snapshot final row (Relates.mem finalRelated row member)
  · exact (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore_reached (reached := reachedIndex) (id := request.binder.id) (type := request.payloadType)
      (value := .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)) initial
      (ProtectedStateTransition.Transition.of_related (protocol headers keys) boundRelated)

end Tests.SourceCoreCallableIndexedOwnedOrdinaryAllocation
