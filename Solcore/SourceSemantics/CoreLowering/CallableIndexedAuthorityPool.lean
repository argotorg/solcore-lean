import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization
import Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationCompletion

/-! Ordered, state-indexed catalogue authorities. Registered snapshots are
exactly the retained Authority.records, not all physical source snapshots.
Physical frames may be shared; keys and records need not be unique. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedAuthorityPool
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog

structure Key {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
    (values : ValuesContext) (definitions : DataEnvironment) (program : Program) where
  locations : Header prepared values definitions program → Location
  capturePrefix : Nat
  frameLocation : Location

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}

structure EntryValid (headers : Inventory prepared values ambient.definitions program)
    (key : Key prepared values ambient.definitions program)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  authority : Authority headers key.locations key.capturePrefix mapping world heap store
  frame_eq : authority.frameLocation = key.frameLocation

structure Pool (headers : Inventory prepared values ambient.definitions program)
    (keys : List (Key prepared values ambient.definitions program))
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  rows : (i : Fin keys.length) → EntryValid headers keys[i.val] mapping world heap store
  separated : ∀ (i j : Fin keys.length) record,
    record ∈ (rows i).authority.records → record.location ≠ keys[j.val].frameLocation

variable {headers : Inventory prepared values ambient.definitions program}
  {keys : List (Key prepared values ambient.definitions program)}
  {key otherKey : Key prepared values ambient.definitions program}
  {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
  {heap after : Dynamic.Heap} {store futureStore : Store}

/-- A conditional bridge from the complete independent authority. -/
def EntryValid.of_authority {locations : Locations} {capturePrefix : Nat}
    (authority : Authority headers locations capturePrefix mapping world heap store) :
    EntryValid headers ⟨locations, capturePrefix, authority.frameLocation⟩ mapping world heap store :=
  ⟨authority, rfl⟩

def EntryValid.extend (entry : EntryValid headers key mapping world heap store)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    EntryValid headers key futureMap futureWorld after futureStore :=
  ⟨entry.authority.extend maps worlds frame metadata, entry.frame_eq⟩

def Pool.extend (pool : Pool headers keys mapping world heap store)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Pool headers keys futureMap futureWorld after futureStore where
  rows i := (pool.rows i).extend maps worlds frame metadata
  separated := pool.separated

/-- A global closure cell cannot be another row's mutable frame, even when
those rows use different catalogue location functions. -/
theorem EntryValid.global_ne_frame (left : EntryValid headers key mapping world heap store)
    (right : EntryValid headers otherKey mapping world heap store)
    {header : Header prepared values ambient.definitions program} (member : header ∈ headers) :
    key.locations header ≠ otherKey.frameLocation := by
  obtain ⟨capture⟩ := left.authority.captures header member
  intro same
  have frameRead := right.authority.frame.read
  rw [right.frame_eq, ← same, capture.read] at frameRead
  cases shape : right.authority.current <;> simp [shape, encode] at frameRead

private def reStore (entry : EntryValid headers key mapping world heap store) (same : store = futureStore) :
    EntryValid headers key mapping world heap futureStore := same ▸ entry

private theorem reStore_records (entry : EntryValid headers key mapping world heap store) (same : store = futureStore) :
    (reStore entry same).authority.records = entry.authority.records := by cases same; rfl

private theorem reStore_current (entry : EntryValid headers key mapping world heap store) (same : store = futureStore) :
    (reStore entry same).authority.current = entry.authority.current := by cases same; rfl

private theorem reStore_ghost (entry : EntryValid headers key mapping world heap store) (same : store = futureStore) :
    (reStore entry same).authority.ghost = entry.authority.ghost := by cases same; rfl

private def installedEntry (entry : EntryValid headers key mapping world heap store)
    (target : EntryValid headers otherKey mapping world heap store)
    (separate : ∀ record ∈ entry.authority.records, record.location ≠ otherKey.frameLocation)
    {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost) :
    EntryValid headers key mapping world heap
      (store.set otherKey.frameLocation (encode prepared.layout.frame next)) := by
  by_cases same : key.frameLocation = otherKey.frameLocation
  · exact reStore ⟨entry.authority.install history, entry.frame_eq⟩
      (by rw [entry.frame_eq, same])
  · have written : store.write? otherKey.frameLocation (encode prepared.layout.frame next) =
        some (store.set otherKey.frameLocation (encode prepared.layout.frame next)) :=
      Store.write?_eq_some_iff.mpr ⟨by
        rw [← target.frame_eq]
        exact (List.getElem?_eq_some_iff.mp target.authority.frame.read).1, rfl⟩
    refine ⟨{ entry.authority with
      frame := ⟨(Store.write?_preserves_other written (by simpa only [entry.frame_eq] using same)).trans
        entry.authority.frame.read, entry.authority.frame.history⟩
      snapshots := ?_
      captures := ?_ }, entry.frame_eq⟩
    · intro record member
      exact (entry.authority.snapshots record member).other_write (separate record member) written
    · intro header member
      obtain ⟨capture⟩ := entry.authority.captures header member
      exact ⟨{ capture with read := (Store.write?_preserves_other written
        (entry.global_ne_frame target member)).trans capture.read }⟩

private theorem installedEntry_records (entry : EntryValid headers key mapping world heap store)
    (target : EntryValid headers otherKey mapping world heap store)
    (separate : ∀ record ∈ entry.authority.records, record.location ≠ otherKey.frameLocation)
    {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost) :
    (installedEntry entry target separate history).authority.records = entry.authority.records := by
  unfold installedEntry
  split
  · exact reStore_records _ _
  · rfl

private theorem installedEntry_current (entry : EntryValid headers key mapping world heap store)
    (target : EntryValid headers otherKey mapping world heap store)
    (separate : ∀ record ∈ entry.authority.records, record.location ≠ otherKey.frameLocation)
    {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost) :
    (installedEntry entry target separate history).authority.current =
      if key.frameLocation = otherKey.frameLocation then next else entry.authority.current := by
  unfold installedEntry
  split
  · rw [reStore_current]; rfl
  · rfl

/-- Update every row sharing the actual physical frame. Other rows retain
all their own current history and all rows retain full captures and records. -/
def Pool.install (pool : Pool headers keys mapping world heap store)
    (selected : Fin keys.length) {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost) :
    Pool headers keys mapping world heap
      (store.set keys[selected.val].frameLocation (encode prepared.layout.frame next)) where
  rows i := installedEntry (pool.rows i) (pool.rows selected)
    (pool.separated i selected) history
  separated i j record member := pool.separated i j record
    (by simpa only [installedEntry_records] using member)

theorem Pool.install_records (pool : Pool headers keys mapping world heap store)
    (selected i : Fin keys.length) {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost) :
    ((pool.install selected history).rows i).authority.records = (pool.rows i).authority.records :=
  installedEntry_records (pool.rows i) (pool.rows selected) (pool.separated i selected) history

theorem Pool.install_current (pool : Pool headers keys mapping world heap store)
    (selected i : Fin keys.length) {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost) :
    ((pool.install selected history).rows i).authority.current =
      if keys[i.val].frameLocation = keys[selected.val].frameLocation then next else (pool.rows i).authority.current :=
  installedEntry_current (pool.rows i) (pool.rows selected) (pool.separated i selected) history

theorem Pool.install_ghost (pool : Pool headers keys mapping world heap store)
    (selected i : Fin keys.length) {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost) :
    ((pool.install selected history).rows i).authority.ghost =
      if keys[i.val].frameLocation = keys[selected.val].frameLocation then nextGhost else (pool.rows i).authority.ghost := by
  change (installedEntry (pool.rows i) (pool.rows selected) (pool.separated i selected) history).authority.ghost = _
  unfold installedEntry
  split
  · rw [reStore_ghost]; rfl
  · rfl

/-- The exact original closure code and full capture environment survive the
frame write, including unused captured values and differing catalogue keys. -/
theorem Pool.install_capture_read (pool : Pool headers keys mapping world heap store)
    (selected i : Fin keys.length) {header : Header prepared values ambient.definitions program}
    (member : header ∈ headers)
    (capture : Capture headers keys[i.val].locations keys[i.val].capturePrefix
      (pool.rows i).authority.frameLocation header mapping world heap store)
    {next : NativeFrame} :
    Store.read? (store.set keys[selected.val].frameLocation (encode prepared.layout.frame next)) (keys[i.val].locations header) =
      some (.inRight .unit (.closure header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured)) := by
  have written : store.write? keys[selected.val].frameLocation (encode prepared.layout.frame next) =
      some (store.set keys[selected.val].frameLocation (encode prepared.layout.frame next)) :=
    Store.write?_eq_some_iff.mpr ⟨by
      rw [← (pool.rows selected).frame_eq]
      exact (List.getElem?_eq_some_iff.mp (pool.rows selected).authority.frame.read).1, rfl⟩
  exact (Store.write?_preserves_other written ((pool.rows i).global_ne_frame (pool.rows selected) member)).trans capture.read

def Pool.singleton (entry : EntryValid headers key mapping world heap store) :
    Pool headers [key] mapping world heap store where
  rows i := by
    have same : i = 0 := by apply Fin.ext; have bound := i.isLt; change i.val < 1 at bound; change i.val = 0; omega
    subst i
    exact entry
  separated i j record member := by
    have hi : i = 0 := by apply Fin.ext; have bound := i.isLt; change i.val < 1 at bound; change i.val = 0; omega
    have hj : j = 0 := by apply Fin.ext; have bound := j.isLt; change j.val < 1 at bound; change j.val = 0; omega
    subst i; subst j
    change record.location ≠ key.frameLocation
    simpa only [entry.frame_eq] using entry.authority.distinct record member

/-- Restoration recovers the original pool domain from the actual body
frame. Newly created body keys need separate explicit registration. -/
theorem Pool.restore (pool : Pool headers keys mapping world heap store)
    (selected : Fin keys.length) {next : NativeFrame}
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    (registered : prepared.layout.frame.Registered ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after futureStore)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping
      (store.set keys[selected.val].frameLocation (encode prepared.layout.frame next)) futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after
      (futureStore.set keys[selected.val].frameLocation (encode prepared.layout.frame (pool.rows selected).authority.current)) ∧
    Nonempty (Pool headers keys futureMap futureWorld after
      (futureStore.set keys[selected.val].frameLocation (encode prepared.layout.frame (pool.rows selected).authority.current))) := by
  let row := pool.rows selected
  obtain ⟨finalHeaps, restored, _⟩ := CallableIndexedBodyFrames.restore registered row.authority.unmapped row.authority.typed
    row.authority.frame heaps worlds (by simpa only [row.frame_eq] using frame)
  rw [row.frame_eq] at finalHeaps restored
  exact ⟨finalHeaps, ⟨pool.extend maps worlds restored metadata⟩⟩


/-- Registration refers to an actual record in an actual retained row. -/
def Pool.Registered (pool : Pool headers keys mapping world heap store)
    (record : CallableIndexedSnapshots.Record) : Prop :=
  ∃ i : Fin keys.length, record ∈ (pool.rows i).authority.records

private def rekey (entry : EntryValid headers key mapping world heap store) (same : key = otherKey) :
    EntryValid headers otherKey mapping world heap store := same ▸ entry

private theorem rekey_records (entry : EntryValid headers key mapping world heap store) (same : key = otherKey) :
    (rekey entry same).authority.records = entry.authority.records := by cases same; rfl

private def appendedRows (pool : Pool headers keys mapping world heap store)
    (entry : EntryValid headers key mapping world heap store)
    (i : Fin (keys ++ [key]).length) :
    EntryValid headers (keys ++ [key])[i.val] mapping world heap store :=
  if h : i.val < keys.length then
    rekey (pool.rows ⟨i.val, h⟩) (by simp only [List.getElem_append_left h])
  else by
    have hi : i.val = keys.length := by have bound := i.isLt; simp only [List.length_append, List.length_singleton] at bound; omega
    exact rekey entry (by simp only [hi, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero])

private theorem appendedRows_records (pool : Pool headers keys mapping world heap store)
    (entry : EntryValid headers key mapping world heap store)
    (i : Fin (keys ++ [key]).length) :
    (appendedRows pool entry i).authority.records =
      if h : i.val < keys.length then (pool.rows ⟨i.val, h⟩).authority.records else entry.authority.records := by
  unfold appendedRows
  split <;> exact rekey_records _ _

private def appendPool (pool : Pool headers keys mapping world heap store)
    (entry : EntryValid headers key mapping world heap store)
    (oldNew : ∀ i record, record ∈ (pool.rows i).authority.records → record.location ≠ key.frameLocation)
    (newOld : ∀ (j : Fin keys.length) record, record ∈ entry.authority.records → record.location ≠ keys[j.val].frameLocation) :
    Pool headers (keys ++ [key]) mapping world heap store where
  rows := appendedRows pool entry
  separated i j record member := by
    rw [appendedRows_records] at member
    by_cases hi : i.val < keys.length
    · simp only [hi, ↓reduceDIte] at member
      by_cases hj : j.val < keys.length
      · simpa only [List.getElem_append_left hj] using pool.separated ⟨i.val, hi⟩ ⟨j.val, hj⟩ record member
      · have hjEq : j.val = keys.length := by have bound := j.isLt; simp only [List.length_append, List.length_singleton] at bound; omega
        simpa only [hjEq, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero] using oldNew ⟨i.val, hi⟩ record member
    · simp only [hi, ↓reduceDIte] at member
      by_cases hj : j.val < keys.length
      · simpa only [List.getElem_append_left hj] using newOld ⟨j.val, hj⟩ record member
      · have hjEq : j.val = keys.length := by have bound := j.isLt; simp only [List.length_append, List.length_singleton] at bound; omega
        simpa only [hjEq, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero, entry.frame_eq] using entry.authority.distinct record member

/-- Reuse a registered physical frame. Every retained new-row record is
already registered; neither a decoder nor a type can supply this provenance. -/
def Pool.register_existing_frame (pool : Pool headers keys mapping world heap store)
    (selected : Fin keys.length) (entry : EntryValid headers key mapping world heap store)
    (sameFrame : key.frameLocation = keys[selected.val].frameLocation)
    (records : ∀ record ∈ entry.authority.records, pool.Registered record) :
    Pool headers (keys ++ [key]) mapping world heap store :=
  appendPool pool entry
    (fun i record member => by simpa only [sameFrame] using pool.separated i selected record member)
    (fun j record member => by obtain ⟨i, contained⟩ := records record member; exact pool.separated i j record contained)

/-- A fresh frame comes from the actual one-cell allocator. Its complete
initialized catalogue remains an independent receipt. All old snapshot
locations are bounded by their original reads, so fresh-frame separation is
proved here. This does not construct new captures from frame allocation. -/
def Pool.register_fresh_frame (pool : Pool headers keys mapping world heap store)
    {next : NativeFrame}
    {allocatedStore : Store} {location : Location}
    (allocated : store.allocate (encode prepared.layout.frame next) = (allocatedStore, location))
    (worlds : WorldExtends world futureWorld)
    (entry : EntryValid headers key mapping futureWorld heap allocatedStore)
    (freshFrame : key.frameLocation = location)
    (records : ∀ record ∈ entry.authority.records, pool.Registered record) :
    Pool headers (keys ++ [key]) mapping futureWorld heap allocatedStore := by
  have storeEq : allocatedStore = store ++ [encode prepared.layout.frame next] := by
    exact (congrArg Prod.fst allocated).symm
  have locationEq : location = store.length := by exact (congrArg Prod.snd allocated).symm
  have frame := AdministrativePreserved.allocate_administrative mapping store (encode prepared.layout.frame next)
  change AdministrativePreserved mapping store mapping (store ++ [encode prepared.layout.frame next]) at frame
  rw [← storeEq] at frame
  let extended := pool.extend (LocationMap.Extends.refl mapping) worlds frame (Dynamic.HeapMetadataExtend.refl heap)
  apply appendPool extended entry
  · intro i record member
    have oldMember : record ∈ (pool.rows i).authority.records := member
    have bound := (List.getElem?_eq_some_iff.mp ((pool.rows i).authority.snapshots record oldMember).read).1
    rw [freshFrame, locationEq]
    exact Nat.ne_of_lt bound
  · intro j record member
    obtain ⟨i, contained⟩ := records record member
    exact pool.separated i j record contained

/-- Record the history of the actual freshly allocated frame. -/
theorem fresh_frame_state {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost)
    {allocatedStore : Store} {location : Location}
    (allocated : store.allocate (encode prepared.layout.frame next) = (allocatedStore, location)) :
    CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location next nextGhost allocatedStore := by
  have read := Store.allocate_fresh_lookup store (encode prepared.layout.frame next)
  rw [allocated] at read
  exact ⟨read, history⟩


private def addRecord (entry : EntryValid headers key mapping world heap store)
    (record : CallableIndexedSnapshots.Record)
    (holds : CallableIndexedSnapshots.Holds prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store record)
    (separate : record.location ≠ key.frameLocation) :
    EntryValid headers key mapping world heap store where
  authority := { entry.authority with
    records := entry.authority.records ++ [record]
    snapshots := by
      intro item member
      rcases List.mem_append.mp member with old | fresh
      · exact entry.authority.snapshots item old
      · have same := List.mem_singleton.mp fresh; subst item; exact holds
    distinct := by
      intro item member
      rcases List.mem_append.mp member with old | fresh
      · exact entry.authority.distinct item old
      · have same := List.mem_singleton.mp fresh; subst item
        simpa only [entry.frame_eq] using separate }
  frame_eq := entry.frame_eq

/-- Register one authenticated snapshot in its selected ordered row. Every
physical frame remains separated from the record's actual snapshot cell. -/
def Pool.record_snapshot (pool : Pool headers keys mapping world heap store)
    (selected : Fin keys.length) (record : CallableIndexedSnapshots.Record)
    (holds : CallableIndexedSnapshots.Holds prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store record)
    (separate : ∀ i : Fin keys.length, record.location ≠ keys[i.val].frameLocation) :
    Pool headers keys mapping world heap store where
  rows i := if i = selected then addRecord (pool.rows i) record holds (separate i) else pool.rows i
  separated i j item member := by
    by_cases same : i = selected
    · simp only [same, ↓reduceIte] at member
      rcases List.mem_append.mp member with old | fresh
      · exact pool.separated i j item old
      · have equal := List.mem_singleton.mp fresh; subst item; exact separate j
    · simp only [same, ↓reduceIte] at member
      exact pool.separated i j item member

theorem Pool.record_snapshot_selected (pool : Pool headers keys mapping world heap store)
    (selected : Fin keys.length) (record : CallableIndexedSnapshots.Record)
    (holds : CallableIndexedSnapshots.Holds prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store record)
    (separate : ∀ i : Fin keys.length, record.location ≠ keys[i.val].frameLocation) :
    ((pool.record_snapshot selected record holds separate).rows selected).authority.records =
      (pool.rows selected).authority.records ++ [record] := by
  simp only [Pool.record_snapshot, ↓reduceIte]
  rfl

theorem Pool.record_snapshot_other (pool : Pool headers keys mapping world heap store)
    (selected : Fin keys.length) (record : CallableIndexedSnapshots.Record)
    (holds : CallableIndexedSnapshots.Holds prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store record)
    (separate : ∀ i : Fin keys.length, record.location ≠ keys[i.val].frameLocation)
    (i : Fin keys.length) (different : i ≠ selected) :
    ((pool.record_snapshot selected record holds separate).rows i).authority.records =
      (pool.rows i).authority.records := by
  simp only [Pool.record_snapshot, different, ↓reduceIte]

/-- Actual three-cell source allocation registers its preceding snapshot.
The snapshot is separated from every old frame by original read bounds;
callers supply no snapshot-vs-frame separation law. -/
theorem Pool.completed_snapshot (pool : Pool headers keys mapping world heap store)
    (selected : Fin keys.length)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request} {globals : Nat}
    {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.layout.frame globals allocate request)
    (same : annotation.original = allocation.expression)
    {environment : Environment} {location : Location} {native : NativeFrame} {ghost : GhostFrame}
    {metadata : Option MetadataState} {payload : Option Value}
    (reference : environment[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef prepared.layout.frame.type location))
    (read : store.read? location = some (encode prepared.layout.frame native))
    (history : Carries prepared.graph.inputs prepared.graph.table native ghost metadata)
    (bounded : ∀ target ∈ mapping, target < store.length)
    (slots : ∀ index binding, request.scope[index]? = some binding → ∃ target,
      environment[request.references index]? = some (.cellRef (OptionalCell.cellType binding.2) target))
    (payloadAt : CallableIndexedAllocationCompletion.PayloadAt request environment payload)
    (worlds : WorldExtends world futureWorld)
    (sourceMetadata : Dynamic.HeapMetadataExtend heap after) :
    ∃ captured,
      Evaluates environment store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [encode prepared.layout.frame native, SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      ∃ result : Pool headers keys (mapping ++ [store.length + 2]) futureWorld after
        (store ++ [encode prepared.layout.frame native, SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]),
        (result.rows selected).authority.records =
          (pool.rows selected).authority.records ++ [⟨store.length, native, ghost, metadata⟩] ∧
        (∀ i, i ≠ selected → (result.rows i).authority.records = (pool.rows i).authority.records) := by
  obtain ⟨captured, evaluated, frame, snapshots⟩ := CallableIndexedAllocationCompletion.preserves prepared.graph
    allocation annotation same reference read history bounded (pool.rows selected).authority.snapshots slots payloadAt
  let extended := pool.extend ⟨[store.length + 2], rfl⟩ worlds frame sourceMetadata
  let record : CallableIndexedSnapshots.Record := ⟨store.length, native, ghost, metadata⟩
  have holds := snapshots record (List.mem_append_right _ (List.mem_singleton_self _))
  have separate : ∀ i : Fin keys.length, record.location ≠ keys[i.val].frameLocation := by
    intro i
    have bound := (List.getElem?_eq_some_iff.mp (pool.rows i).authority.frame.read).1
    rw [(pool.rows i).frame_eq] at bound
    exact Nat.ne_of_gt bound
  refine ⟨captured, evaluated, extended.record_snapshot selected record holds separate, ?_, ?_⟩
  · exact Pool.record_snapshot_selected _ _ _ _ _
  · intro i different
    exact Pool.record_snapshot_other _ _ _ _ _ i different

/-- Equal keys and shared physical frames are retained as separate ordered
rows. The duplicate is registered through the ordinary frame-reuse producer. -/
def Pool.duplicate (pool : Pool headers keys mapping world heap store) (selected : Fin keys.length) :
    Pool headers (keys ++ [keys[selected.val]]) mapping world heap store :=
  pool.register_existing_frame selected (pool.rows selected) rfl (fun _ member => ⟨selected, member⟩)

/-- The real prepared recipe constructs the initial authority. The returned
pool keeps exactly that entry and its full initial catalogue. -/
theorem initial_entry (compiled : SourceCoreUnifiedCompilation.Compiled)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    (headers : Inventory compiled.indexed.ancestry values ambient.definitions program)
    (ledger : Ledger headers compiled.indexed.secondPass.closures)
    (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
    (locals : ∀ header, header ∈ headers → header.function.context.locals = [])
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩
        (RecursiveNamedCatalogPreparedInitialization.store compiled) ∧
      ∃ entry : Entry headers
        (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
        0 0 [] [] world ⟨[]⟩ (RecursiveNamedCatalogPreparedInitialization.store compiled)
        (RecursiveNamedCatalogPreparedInitialization.environment compiled),
        Nonempty (Pool headers [⟨(fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot),
          0, entry.authority.frameLocation⟩] [] world ⟨[]⟩ (RecursiveNamedCatalogPreparedInitialization.store compiled)) := by
  obtain ⟨world, heaps, ⟨entry⟩⟩ := RecursiveNamedCatalogPreparedInitialization.entry compiled headers ledger sizes locals
    accepted definitions functions registry
  exact ⟨world, heaps, entry, ⟨Pool.singleton (EntryValid.of_authority entry.authority)⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedAuthorityPool
