import Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionEntries

/-! Actual owned pools provide protected state witnesses. The observation is
the complete ordered record list in every ordered key row. Related witnesses
append to each row, preserving its original order and multiplicity. Actual
allocation produces records; administrative transport and frame restoration
retain the reached lists exactly. No body execution law is supplied here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedAuthorityPool CallableIndexedOwnedFunctionEntries

abbrev Records {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)) :=
  Fin keys.length → List CallableIndexedSnapshots.Record

abbrev State {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program))
    (index : ProtectedStateTransition.Index) :=
  OwnedPool headers keys index.mapping index.world index.heap index.store

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

def records {index : ProtectedStateTransition.Index} (state : State headers keys index) : Records keys :=
  fun i => (state.rows i).authority.records

/-- Prefix equality retains every original position, including duplicates. -/
def RecordPrefix (initial reached : List CallableIndexedSnapshots.Record) : Prop :=
  ∃ suffix, reached = initial ++ suffix

theorem RecordPrefix.refl (items : List CallableIndexedSnapshots.Record) : RecordPrefix items items :=
  ⟨[], (List.append_nil items).symm⟩

theorem RecordPrefix.trans {initial middle reached : List CallableIndexedSnapshots.Record}
    (left : RecordPrefix initial middle) (right : RecordPrefix middle reached) :
    RecordPrefix initial reached := by
  obtain ⟨first, firstEq⟩ := left
  obtain ⟨last, lastEq⟩ := right
  exact ⟨first ++ last, by rw [lastEq, firstEq, List.append_assoc]⟩

theorem RecordPrefix.mem {initial reached : List CallableIndexedSnapshots.Record}
    (retained : RecordPrefix initial reached) {record : CallableIndexedSnapshots.Record}
    (member : record ∈ initial) : record ∈ reached := by
  obtain ⟨suffix, same⟩ := retained
  rw [same]
  exact List.mem_append_left suffix member

def Relates {initial reached : ProtectedStateTransition.Index}
    (before : State headers keys initial) (after : State headers keys reached) : Prop :=
  ∀ i : Fin keys.length, RecordPrefix (records before i) (records after i)

theorem Relates.refl {index : ProtectedStateTransition.Index} (state : State headers keys index) :
    Relates state state :=
  fun i => RecordPrefix.refl (records state i)

theorem Relates.trans {initial middle reached : ProtectedStateTransition.Index}
    {before : State headers keys initial} {during : State headers keys middle} {after : State headers keys reached}
    (first : Relates before during) (last : Relates during after) : Relates before after :=
  fun i => RecordPrefix.trans (first i) (last i)

theorem Relates.of_records_eq {initial reached : ProtectedStateTransition.Index}
    {before : State headers keys initial} {after : State headers keys reached}
    (same : records after = records before) : Relates before after := by
  intro i
  rw [same]
  exact RecordPrefix.refl (records before i)

theorem Relates.mem {initial reached : ProtectedStateTransition.Index}
    {before : State headers keys initial} {after : State headers keys reached}
    (related : Relates before after) (i : Fin keys.length) {record : CallableIndexedSnapshots.Record}
    (member : record ∈ records before i) : record ∈ records after i :=
  RecordPrefix.mem (related i) member

def protocol (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)) :
    ProtectedStateTransition.Protocol (Records keys) where
  State := State headers keys
  records := records
  Relates := Relates
  refl := Relates.refl
  trans := Relates.trans

/-- Ordinary administrative effects keep the exact observation, including
the order and multiplicity of all rows and their full record lists. -/
def administrativeTransport (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)) :
    ProtectedStateTransition.AdministrativeTransport (protocol headers keys) where
  extend := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    state.extend maps worlds frame metadata
  related := fun {_initial} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata =>
    Relates.of_records_eq rfl
  records_eq := fun {_initial} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata => rfl

theorem administrative_records {index : ProtectedStateTransition.Index} (state : State headers keys index)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (maps : LocationMap.Extends index.mapping mapping) (worlds : WorldExtends index.world world)
    (frame : AdministrativePreserved index.mapping index.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend index.heap heap) :
    records ((administrativeTransport headers keys).extend state maps worlds frame metadata) = records state := rfl

theorem record_snapshot {index : ProtectedStateTransition.Index} (state : State headers keys index)
    (i : Fin keys.length) {record : CallableIndexedSnapshots.Record} (member : record ∈ records state i) :
    CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame index.mapping index.store record :=
  (state.rows i).authority.snapshots record member

theorem record_location_lt {index : ProtectedStateTransition.Index} (state : State headers keys index)
    (i : Fin keys.length) {record : CallableIndexedSnapshots.Record} (member : record ∈ records state i) :
    record.location < index.store.length :=
  (List.getElem?_eq_some_iff.mp (record_snapshot state i member).read).1

theorem fresh_record_absent {index : ProtectedStateTransition.Index} (state : State headers keys index)
    (i : Fin keys.length) {record : CallableIndexedSnapshots.Record}
    (fresh : record.location = index.store.length) : record ∉ records state i := by
  intro member
  have bound := record_location_lt state i member
  rw [fresh] at bound
  exact Nat.lt_irrefl _ bound

section Allocation
variable {index : ProtectedStateTransition.Index} (state : State headers keys index) (selected : Fin keys.length)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request} {globals : Nat}
  {allocate : SourceCoreSourceCells.Allocator}
  (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame globals allocate request)
  (same : annotation.original = allocation.expression)
  {environment : Environment} {location : Location} {native : NativeFrame} {ghost : GhostFrame}
  {metadata : Option MetadataState} {payload : Option Value}
  (reference : environment[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
  (read : index.store.read? location = some (encode compiled.indexed.ancestry.layout.frame native))
  (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
  (bounded : ∀ target ∈ index.mapping, target < index.store.length)
  (slots : ∀ position binding, request.scope[position]? = some binding → ∃ target,
    environment[request.references position]? = some (.cellRef (OptionalCell.cellType binding.2) target))
  (payloadAt : CallableIndexedAllocationCompletion.PayloadAt request environment payload)
  {world : StoreTyping} {heap : Dynamic.Heap}
  (worlds : WorldExtends index.world world) (sourceMetadata : Dynamic.HeapMetadataExtend index.heap heap)

include same reference read history bounded slots payloadAt worlds sourceMetadata

/-- The actual three-cell evaluation adds one snapshot to the selected row.
All other rows keep their complete lists; the returned pool is the actual
post-witness used by subsequent transitions. -/
theorem completed_snapshot :
    ∃ captured,
      Evaluates environment index.store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (index.store.length + 2))
        (index.store ++ [encode compiled.indexed.ancestry.layout.frame native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      ∃ final : State headers keys (index.extend (index.mapping ++ [index.store.length + 2]) world heap
          (index.store ++ [encode compiled.indexed.ancestry.layout.frame native,
            SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
            CallableIndexedAllocationCompletion.optionalValue request.payloadType payload])),
        Relates state final ∧
        records final selected = records state selected ++ [⟨index.store.length, native, ghost, metadata⟩] ∧
        (∀ i, i ≠ selected → records final i = records state i) ∧
        CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame (index.mapping ++ [index.store.length + 2])
          (index.store ++ [encode compiled.indexed.ancestry.layout.frame native,
            SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
            CallableIndexedAllocationCompletion.optionalValue request.payloadType payload])
          ⟨index.store.length, native, ghost, metadata⟩ := by
  obtain ⟨captured, evaluated, final, appended, unchanged⟩ := state.completed_snapshot selected
    allocation annotation same reference read history bounded slots payloadAt worlds sourceMetadata
  refine ⟨captured, evaluated, final, ?_, appended, unchanged, ?_⟩
  · intro i
    by_cases selectedRow : i = selected
    · subst i
      exact ⟨[⟨index.store.length, native, ghost, metadata⟩], appended⟩
    · exact ⟨[], by simpa only [records, List.append_nil] using unchanged i selectedRow⟩
  · apply (final.rows selected).authority.snapshots
    rw [appended]
    exact List.mem_append_right _ (List.mem_singleton_self _)

end Allocation

section FrameUpdates
variable {index : ProtectedStateTransition.Index} (state : State headers keys index) (selected : Fin keys.length)
  {next : NativeFrame} {nextGhost : GhostFrame}
  (history : Current compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next nextGhost)

include history

def install : State headers keys (index.extend index.mapping index.world index.heap
    (index.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))) :=
  state.install selected history

theorem install_records : records (install state selected history) = records state := by
  funext i
  exact Pool.install_records state selected i history

theorem install_related : Relates state (install state selected history) :=
  Relates.of_records_eq (install_records state selected history)

theorem install_transition : ProtectedStateTransition.Transition (protocol headers keys) state
    (index.extend index.mapping index.world index.heap
      (index.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))) :=
  ⟨install state selected history, install_related state selected history⟩

end FrameUpdates

section Restoration
variable {initial reached : ProtectedStateTransition.Index}
  (saved : State headers keys initial) (after : State headers keys reached) (selected : Fin keys.length)

/-- Restoration uses the reached pool as its baseline. Any records created
between the saved and reached points remain in their exact original order. -/
def restored : State headers keys (reached.extend reached.mapping reached.world reached.heap
    (reached.store.set keys[selected.val].frameLocation
      (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current))) :=
  restored_pool saved after selected

theorem restored_records : records (restored saved after selected) = records after := by
  funext i
  exact CallableIndexedOwnedFunctionEntries.restored_records saved after selected i

theorem restored_related : Relates after (restored saved after selected) :=
  Relates.of_records_eq (restored_records saved after selected)

theorem restored_transition : ProtectedStateTransition.Transition (protocol headers keys) after
    (reached.extend reached.mapping reached.world reached.heap
      (reached.store.set keys[selected.val].frameLocation
        (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current))) :=
  ⟨restored saved after selected, restored_related saved after selected⟩

theorem restored_from_saved (retained : Relates saved after) : Relates saved (restored saved after selected) :=
  Relates.trans retained (restored_related saved after selected)

theorem restored_same_frame (i : Fin keys.length)
    (same : keys[i.val].frameLocation = keys[selected.val].frameLocation) :
    ((restored saved after selected).rows i).authority.current = (saved.rows selected).authority.current ∧
    ((restored saved after selected).rows i).authority.ghost = (saved.rows selected).authority.ghost :=
  CallableIndexedOwnedFunctionEntries.restored_same_frame saved after selected i same

theorem restored_other_frame (i : Fin keys.length)
    (different : keys[i.val].frameLocation ≠ keys[selected.val].frameLocation) :
    ((restored saved after selected).rows i).authority.current = (after.rows i).authority.current ∧
    ((restored saved after selected).rows i).authority.ghost = (after.rows i).authority.ghost :=
  CallableIndexedOwnedFunctionEntries.restored_other_frame saved after selected i different

theorem restored_snapshot (i : Fin keys.length) {record : CallableIndexedSnapshots.Record}
    (member : record ∈ records after i) :
    CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame reached.mapping
      (reached.store.set keys[selected.val].frameLocation
        (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current)) record :=
  CallableIndexedOwnedFunctionEntries.restored_snapshot saved after selected i member

theorem restored_capture_read (i : Fin keys.length)
    {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers)
    (capture : RecursiveNamedCatalog.Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers keys[i.val].locations keys[i.val].capturePrefix (after.rows i).authority.frameLocation
      header reached.mapping reached.world reached.heap reached.store) :
    Store.read? (reached.store.set keys[selected.val].frameLocation
      (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current))
      (keys[i.val].locations header) = some (.inRight .unit
        (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
          (header.code.rename capture.embedding.lift) capture.captured)) :=
  CallableIndexedOwnedFunctionEntries.restored_capture_read saved after selected i member capture

/-- Restore the saved physical cell once through the actual completed frame,
returning the reached pool with unchanged full records and the same function
model's final heap correspondence. -/
theorem restore_reached {next : NativeFrame}
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry}
    (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      reached.mapping reached.world reached.heap reached.store)
    (worlds : WorldExtends initial.world reached.world)
    (frame : AdministrativePreserved initial.mapping
      (initial.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))
      reached.mapping reached.store) :
    ∃ final : State headers keys (reached.extend reached.mapping reached.world reached.heap
        (reached.store.set keys[selected.val].frameLocation
          (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current))),
      final = restored saved after selected ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        reached.mapping reached.world reached.heap
        (reached.store.set keys[selected.val].frameLocation
          (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current)) ∧
      AdministrativePreserved initial.mapping initial.store reached.mapping
        (reached.store.set keys[selected.val].frameLocation
          (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current)) ∧
      CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        compiled.indexed.ancestry.layout.frame keys[selected.val].frameLocation
        (saved.rows selected).authority.current (saved.rows selected).authority.ghost
        (reached.store.set keys[selected.val].frameLocation
          (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current)) ∧
      Relates after final ∧ records final = records after := by
  obtain ⟨final, finalEq, finalHeaps, preserved, cell, _, _, _, _⟩ :=
    restore_reached_pool saved after selected registered heaps worlds frame
  exact ⟨final, finalEq, finalHeaps, preserved, cell,
    by rw [finalEq]; exact restored_related saved after selected,
    by rw [finalEq]; exact restored_records saved after selected⟩

end Restoration

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionState
