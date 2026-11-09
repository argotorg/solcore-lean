import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallBounds
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LambdaViewsAndMarkedCaptures
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedBareAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping

/-!
# Indexed callables: authority and origins

`CallableIndexedAuthorityPool`, stage origins, actual named Source receipts, and the runtime entry and preservation of lambdas.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts
/-! Actual cached preparation and the accepted indexed hook select the same
complete named specialization. Source attribution uses this factory record
and the independent named agreement. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

private theorem prepared_key {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {row : SourceSpecialization.SpecializedFunction} {named : SourceCoreGeneralFunctions.Function}
    (accepted : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation row = .ok named) :
    named.signature.key = row.key := by
  unfold SourceCoreGeneralFunctions.prepareFunctionWithRepresentation at accepted
  obtain ⟨discarded, _, accepted⟩ := bind_ok accepted
  cases discarded
  by_cases staged : (row.function.returnComptime && !representation.allowStaged) = true
  · simp [staged, throw, bind, Except.bind] at accepted
  · simp only [staged] at accepted
    cases shape : row.function.type <;>
      simp only [shape, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted <;>
      try contradiction
    rename_i parameter result
    by_cases mismatch : result ≠ row.function.inferredBodyType
    · simp [mismatch] at accepted
    · simp only [mismatch, ↓reduceIte] at accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      cases accepted
      rfl

/-- The canonical sidecar contains its actual exact selection equation. -/
theorem sidecar_record {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {sidecar : SourceCoreStageContracts.Sidecar}
    (accepted : SourceCoreStageContracts.prepareSidecar plan key = .ok sidecar) :
    SourceCompilationPlan.exactSpecialization plan key = .ok sidecar.caller := by
  unfold SourceCoreStageContracts.prepareSidecar at accepted
  cases selected : SourceCompilationPlan.exactSpecialization plan key with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok caller =>
    simp only [selected, Except.mapError, bind, Except.bind] at accepted
    cases valid : SourceCompilationPlan.validateSpecializationMetadataWith true caller with
    | error error => simp [valid, Functor.discard, Functor.mapConst, Except.map] at accepted
    | ok value =>
      simp only [valid] at accepted
      dsimp [Functor.discard, Functor.mapConst, Except.map] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted; rfl
        · cases accepted

private theorem exact_member {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {original candidate : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok original)
    (member : candidate ∈ plan.specializations) (same : candidate.key = key) : candidate = original := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted
  · cases accepted
  · next selected found =>
    cases accepted
    have retained : candidate ∈ plan.specializations.filter (fun item => decide (item.key = key)) :=
      List.mem_filter.mpr ⟨member, by simpa using same⟩
    rw [found] at retained
    exact List.mem_singleton.mp retained
  · cases accepted

/-- The actual hook authenticates its original named sidecar. The retained
compiler receipt determines the key; no scope identity is assumed. -/
theorem hook_sidecar (compiled : SourceCoreUnifiedCompilation.Compiled)
    {named : SourceCoreGeneralFunctions.Function} {body output : Expr}
    (hook : SourceCoreCallableIndexedAncestry.namedBody compiled.indexed.ancestry named body = .ok output) :
    ∃ sidecar, SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      named.signature.key = .ok sidecar := by
  obtain ⟨origin, _, selected, _, _⟩ := CallableIndexedFormation.namedBody_receipt compiled.indexed.ancestry hook
  let table := compiled.indexed.ancestry.graph.inputs.callable.table
  have owned : table.idAt? (.named named.signature.key) = some origin := selected
  cases made : SourceCoreCallableContracts.descriptor table (.named named.signature.key) with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at made
    split at made
    · next absent => rw [owned] at absent; cases absent
    · cases made
  | ok descriptor =>
    obtain ⟨entry, member, originEq, _⟩ := CallEntryCertificates.descriptor_entry descriptor
    have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
      compiled.indexed.ancestry.graph.inputs.callableSelected
    have authenticated := CallEntryCertificates.prepareWithProjection_authenticates prepared.accepted entry member
    unfold CallEntryCertificates.Authenticated at authenticated
    rw [originEq] at authenticated
    generalize countEq : entry.parameterCount = count at authenticated
    generalize contractEq : entry.contract = contract at authenticated
    cases authenticated with
    | named accepted =>
      obtain ⟨receipt⟩ := CallContractCertificates.named_of_accepted accepted
      exact ⟨receipt.sidecar, receipt.prepared⟩

/-- The actual table authenticates the named entry selected by this hook. -/
theorem hook_record_exists (compiled : SourceCoreUnifiedCompilation.Compiled)
    {named : SourceCoreGeneralFunctions.Function} {body output : Expr}
    (hook : SourceCoreCallableIndexedAncestry.namedBody compiled.indexed.ancestry named body = .ok output) :
    ∃ row, SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok row := by
  obtain ⟨sidecar, issued⟩ := hook_sidecar compiled hook
  exact ⟨sidecar.caller, sidecar_record issued⟩

/-- Cached full-row preparation identifies the exact record selected by the
same hook, including every source node and ordered requirement row. -/
theorem cached_record (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function} {body output : Expr}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (hook : SourceCoreCallableIndexedAncestry.namedBody compiled.indexed.ancestry named body = .ok output) :
    SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized := by
  obtain ⟨row, member, prepared⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled selected
  have namedEq := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs prepared).1
  have key := prepared_key prepared
  have member : row ∈ compiled.indexed.base.plan.specializations := by
    rw [CallableIndexedPreparedInventories.indexed_base compiled.indexedPrepared]
    exact List.mem_reverse.mp (List.mem_of_getElem? member)
  obtain ⟨original, found⟩ := hook_record_exists compiled hook
  have same := exact_member found member key.symm
  rw [namedEq, same]
  exact found

variable {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : Program}

/-- The cached slot and accepted hook are fields of the original header. -/
theorem header_record (compiled : SourceCoreUnifiedCompilation.Compiled)
    (header : RecursiveNamedCatalog.Header compiled.indexed.ancestry values definitions program) :
    SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan header.named.signature.key = .ok header.named.specialized :=
  cached_record compiled header.selected header.hook

/-- Named agreement transports only the independently authenticated source. -/
theorem header_source (compiled : SourceCoreUnifiedCompilation.Compiled)
    (header : RecursiveNamedCatalog.Header compiled.indexed.ancestry values definitions program) :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      header.named.signature.key [] header.function.source ∧ NodeOccurrencesUnique header.function.source := by
  refine ⟨?_, header.unique⟩
  rw [header.agreement.source]
  exact .original (header_record compiled header)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedAuthorityPool
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedStageOrigins
/-! Actual indexed function leaves retain source preparation alongside their
same Code and History. The real stage table turns those static receipts into
callsite coverage under the same ambient function model. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedStageOrigins
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaRuntimeValues

variable {values : SourceCoreCompatibleValues.Context}
  (indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked)

/-- Source preparation is separate from the captured history and native type. -/
def provenanceCondition (checkedProgram : CheckedProgram) (support : SupportFamily indexed)
    (prior : SupportCondition indexed support) : SupportCondition indexed support :=
  fun {_ _ function _ _} captured code history body =>
    prior captured code history body ∧
    LambdaSourceAlignment.SourceReceipt checkedProgram indexed.base.plan
      code.compilation.owner code.active function.source ∧ NodeOccurrencesUnique function.source

theorem provenance_stable (checkedProgram : CheckedProgram) (support : SupportFamily indexed)
    (prior : SupportCondition indexed support)
    (stable : ∀ {mapping futureMapping world futureWorld function scope actual}
      (captured : Captures indexed mapping world scope function.captured actual)
      (code : Code indexed function scope captured.administrative) (history : History code) (body : support code),
      prior captured code history body →
      ∀ (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld),
      prior (captured.extend maps worlds) code history body)
    {mapping futureMapping world futureWorld function scope actual}
    (captured : Captures indexed mapping world scope function.captured actual)
    (code : Code indexed function scope captured.administrative) (history : History code) (body : support code)
    (supported : provenanceCondition indexed checkedProgram support prior captured code history body)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    provenanceCondition indexed checkedProgram support prior (captured.extend maps worlds) code history body :=
  ⟨stable captured code history body supported.1 maps worlds, supported.2⟩

/-- The retained branch keeps its actual parameter order and full dictionary. -/
theorem retained_origin {checkedProgram : CheckedProgram}
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (accepted : SourceCoreStageCodebook.prepareWithProjection checkedProgram indexed.base.plan project limits firstId =
      .ok indexed.ancestry.graph.inputs.callable.table)
    {world : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {carrier : Value} {type : Ty}
    (related : CallableIndexedRetainedNamedValues.Represents indexed world sourceType source carrier type) :
    CallableLedger.OriginRep indexed.base.plan indexed.ancestry.graph.inputs.callable.table source carrier := by
  cases related with
  | retained canonical =>
    cases canonical with
    | builtin builtin =>
      cases builtin with
      | builtin selected number descriptor typed =>
        exact RecursiveStageProjection.builtin_origin accepted descriptor _
    | named row number projection descriptor native =>
      apply RecursiveStageProjection.named_origin accepted descriptor
      simpa only [CallableNamedReversal.global, CallableNamedReversal.target_reverse,
        CallableNamedMetadata.global] using row.target

/-- Only function-leaf constructors are inspected. Data representation keeps
its existing single induction in CompatibleAmbientStageOrigins. -/
theorem origin_of_represents {checkedProgram : CheckedProgram}
    {support : SupportFamily indexed} {prior : SupportCondition indexed support}
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (accepted : SourceCoreStageCodebook.prepareWithProjection checkedProgram indexed.base.plan project limits firstId =
      .ok indexed.ancestry.graph.inputs.callable.table)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty}
    (related : RepresentsWith indexed support (provenanceCondition indexed checkedProgram support prior)
      mapping world sourceType source carrier type) :
    CallableLedger.OriginRep indexed.base.plan indexed.ancestry.graph.inputs.callable.table source carrier := by
  cases related with
  | retained prior => exact retained_origin indexed accepted prior
  | lambda captured code history body supported typed =>
    exact CompatibleAmbientStageOrigins.actual_lambda_origin accepted code.descriptor supported.2.1
      code.viewOfSource supported.2.2 code.found (code.form.trans code.sourceForm) _

section Coverage
variable {checkedProgram : CheckedProgram} {support : SupportFamily indexed}
  {prior : SupportCondition indexed support}
  (stable : ∀ {mapping futureMapping world futureWorld function scope actual}
    (captured : Captures indexed mapping world scope function.captured actual)
    (code : Code indexed function scope captured.administrative) (history : History code) (body : support code),
    prior captured code history body →
    ∀ (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld),
    prior (captured.extend maps worlds) code history body)
  (profile : values.checked.catalog.callableContracts = true)

abbrev model : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions indexed) :=
  modelWith indexed support (provenanceCondition indexed checkedProgram support prior)
    (provenance_stable indexed checkedProgram support prior stable) profile

theorem function_origins {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (accepted : SourceCoreStageCodebook.prepareWithProjection checkedProgram indexed.base.plan project limits firstId =
      .ok indexed.ancestry.graph.inputs.callable.table)
    {registry : SourceCoreRawMetadata.Registry} {sidecar : SourceCoreStageContracts.Sidecar}
    {site : SourceCoreCallableContracts.Callsite}
    (samePlan : sidecar.plan = indexed.base.plan)
    (sameTable : site.table = indexed.ancestry.graph.inputs.callable.table) :
    CompatibleAmbientStageOrigins.FunctionOrigins
      (model indexed stable profile (checkedProgram := checkedProgram)) registry sidecar site := by
  intro mapping world sourceType source carrier type related
  rw [samePlan, sameTable]
  exact origin_of_represents indexed accepted related

end Coverage

private theorem callsite_table {table : SourceCoreStageCodebook.Table}
    {owner : SourceSpecialization.SpecializationKey} {call : ExpressionId}
    {reasonAt : SourceCoreCallableContracts.ReasonAt} {site : SourceCoreCallableContracts.Callsite}
    (issued : SourceCoreCallableContracts.prepareCallsite table owner call reasonAt = .ok site) :
    site.table = table := by
  unfold SourceCoreCallableContracts.prepareCallsite at issued
  split at issued
  · cases issued; rfl
  · cases issued

/-- Public preparation fixes both tables and the full sidecar plan. Function
origins are derived from this same model, rather than supplied as a law. -/
theorem actual_coverage
    (compiled : SourceCoreUnifiedCompilation.Compiled)
    {support : SupportFamily (values := .initial compiled.compatible.checked) compiled.indexed}
    {prior : SupportCondition (values := .initial compiled.compatible.checked) compiled.indexed support}
    (stable : ∀ {mapping futureMapping world futureWorld function scope actual}
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code) (body : support code),
      prior captured code history body →
      ∀ (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld),
      prior (captured.extend maps worlds) code history body)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {native : SourceCoreGeneralFunctions.CallableContext}
    (prepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    {context : SourceCoreFunctions.Context} {node : ExpressionNode} {callee : ExpressionId}
    {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {site : SourceCoreCallableContracts.Callsite} {sidecar : SourceCoreStageContracts.Sidecar}
    (issued : SourceCoreCallableContracts.prepareCallsite native.table context.owner node.id
      native.diagnostics.reasonAt = .ok site)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan context.owner = .ok sidecar)
    (contains : ContainsExpression sidecar.source node.id node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (registry : SourceCoreRawMetadata.Registry) (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (model (values := .initial compiled.compatible.checked) compiled.indexed stable profile (checkedProgram := compiled.sourceProgram)))
      (CallableLedger.frame sidecar) site node.id arguments sourceType type := by
  have sameNative : native = compiled.indexed.ancestry.graph.inputs.callable :=
    Option.some.inj (prepared.present.symm.trans compiled.indexed.ancestry.graph.inputs.callableSelected)
  have accepted := prepared.accepted
  rw [sameNative] at accepted
  intro mapping world source carrier contract represented bound
  exact CompatibleAmbientStageOrigins.actual_coverage (rawRegistry := registry)
    (functions := model (values := .initial compiled.compatible.checked) compiled.indexed stable profile
      (checkedProgram := compiled.sourceProgram)) prepared issued caller contains form
    (function_origins (values := .initial compiled.compatible.checked) compiled.indexed stable profile accepted
      (CallContractCertificates.sidecar_of_accepted caller).1
      ((callsite_table issued).trans (congrArg SourceCoreGeneralFunctions.CallableContext.table sameNative))) sourceType type represented bound

/-- The indexed artifact already retains its present callable context.
This entry constructs the real stage preparation receipt internally. -/
theorem actual_compiled_coverage
    (compiled : SourceCoreUnifiedCompilation.Compiled)
    {support : SupportFamily (values := .initial compiled.compatible.checked) compiled.indexed}
    {prior : SupportCondition (values := .initial compiled.compatible.checked) compiled.indexed support}
    (stable : ∀ {mapping futureMapping world futureWorld function scope actual}
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code) (body : support code),
      prior captured code history body →
      ∀ (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld),
      prior (captured.extend maps worlds) code history body)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {context : SourceCoreFunctions.Context} {node : ExpressionNode} {callee : ExpressionId}
    {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {site : SourceCoreCallableContracts.Callsite} {sidecar : SourceCoreStageContracts.Sidecar}
    (issued : SourceCoreCallableContracts.prepareCallsite compiled.indexed.ancestry.graph.inputs.callable.table context.owner node.id
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.reasonAt = .ok site)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan context.owner = .ok sidecar)
    (contains : ContainsExpression sidecar.source node.id node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (registry : SourceCoreRawMetadata.Registry) (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (model (values := .initial compiled.compatible.checked) compiled.indexed stable profile (checkedProgram := compiled.sourceProgram)))
      (CallableLedger.frame sidecar) site node.id arguments sourceType type := by
  have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  intro mapping world source carrier contract represented bound
  exact actual_coverage compiled stable profile prepared issued caller contains form registry sourceType type represented bound

section Formation
open ReadOnly RecursiveNamedLambdaFormationHeads RecursiveNamedLambdaFormationEntries

variable {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {caller : RecursiveNamedCatalog.Header indexed.ancestry values indexed.layouts.definitions program}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : LambdaWith expressionSyntax certificates (registry := registry) (faults := faults)
    caller context evidence scope id lowered)
  {compilation : SourceCoreFunctions.Context} {capturePrefix : Nat}
  (header : FormationHeader (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller compilation capturePrefix)

include header in
/-- The ordinary generation site supplies its original source preparation;
the static body independently supplies uniqueness of the complete source. -/
theorem formation_receipt (checkedProgram : CheckedProgram) (environment : Dynamic.Environment) :
    LambdaSourceAlignment.SourceReceipt checkedProgram indexed.base.plan
      (head.actualCode environment).compilation.owner (head.actualCode environment).active
      (head.formed environment).source ∧ NodeOccurrencesUnique (head.formed environment).source := by
  constructor
  · change LambdaSourceAlignment.SourceReceipt checkedProgram indexed.base.plan
      head.code.compilation.owner head.code.active (CallableIndexedNamedGeneration.source caller.named)
    rw [head.compilation, head.active]
    exact .original header.record
  · exact (head.actualBody environment).unique

variable {headers : RecursiveNamedCatalog.Inventory indexed.ancestry values indexed.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := indexed.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (program := program)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {ξ : Renaming}
  (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
  (globals : caller.globals = indexed.base.globals.length)
  (slots : ∀ other, other ∈ headers → other.slot < indexed.base.globals.length)
  (entry : RecursiveNamedLambdaFormationEntries.Entry
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1
    scope mapping world heap store canonical)
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative scope environment canonical indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions)

abbrev bodySupport : SupportFamily indexed :=
  fun code => CallableIndexedLambdaStaticBodySupport.BodyWith expressionSyntax certificates code program registry faults

abbrev capturePrior : SupportCondition indexed
    (bodySupport indexed (expressionSyntax := expressionSyntax) (certificates := certificates)
      (program := program) (registry := registry) (faults := faults)) :=
  captureCondition indexed program _ (fun _ _ => True) (headers := headers) (locations := locations) 1

include header slots in
/-- Both origin and capture conditions are built at this actual formation.
No relation on an already represented weak heap is strengthened. -/
theorem formation_condition (checkedProgram : CheckedProgram) :
    provenanceCondition indexed checkedProgram
      (bodySupport indexed (expressionSyntax := expressionSyntax) (certificates := certificates)
        (program := program) (registry := registry) (faults := faults))
      (capturePrior indexed (headers := headers) (locations := locations)
        (expressionSyntax := expressionSyntax) (certificates := certificates) (registry := registry) (faults := faults))
      (captures complete globals entry related agrees typed) (head.actualCode environment)
      (head.history entry environment) (head.actualBody environment) := by
  exact ⟨head.capture_condition (fun _ _ => True) complete globals slots entry related agrees typed trivial,
    formation_receipt indexed head header checkedProgram environment⟩

variable (profile : values.checked.catalog.callableContracts = true)
  (stored : RuntimeStoreHasTypes world store indexed.layouts.definitions)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog values.checked.catalog) projects
    indexed.layouts.definitions}
  (heaps : GenericHeap.HeapRepresents model mapping world heap store)

include header slots in
/-- The formed closure keeps both conditions: the copies keep the catalog
slots past the scope, and the source and its preparation are unchanged. -/
theorem formed_condition (checkedProgram : CheckedProgram)
    (formed : Formed model (captures complete globals entry related agrees typed) (head.actualCode environment)
      (head.history entry environment) heap store entry.catalog.authority.frameLocation) :
    provenanceCondition indexed checkedProgram
      (bodySupport indexed (expressionSyntax := expressionSyntax) (certificates := certificates)
        (program := program) (registry := registry) (faults := faults))
      (capturePrior indexed (headers := headers) (locations := locations)
        (expressionSyntax := expressionSyntax) (certificates := certificates) (registry := registry) (faults := faults))
      (function := formed.closure) formed.captures formed.closureCode formed.closureHistory
      (head.actualBody formed.captured) :=
  ⟨⟨trivial, entry.catalog.authority.frameLocation,
      (capture_globals complete globals slots entry related agrees typed).of_slots formed.slots⟩,
    formation_receipt indexed head header checkedProgram formed.captured⟩

include header slots profile stored heaps in
/-- Source formation and native formation copy the same captured cells and
retain the same actual full store under the stronger static predicate. -/
theorem formation (checkedProgram : CheckedProgram) :
    ∃ formed : Formed model (captures complete globals entry related agrees typed) (head.actualCode environment)
        (head.history entry environment) heap store entry.catalog.authority.frameLocation,
      Dynamic.ExpressionEvaluates program context evidence (head.formed environment).source environment heap
        (head.actualCode environment).id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store ((head.actualCode environment).lowered.expression.rename
          (captures complete globals entry related agrees typed).embedding)
        (.inRight .word (value (head.actualCode environment) formed.embedding (head.history entry environment).native
          formed.closureActual)) formed.finalStore ∧
      RepresentsWith indexed (bodySupport indexed (expressionSyntax := expressionSyntax) (certificates := certificates)
          (program := program) (registry := registry) (faults := faults))
        (provenanceCondition indexed checkedProgram _ (capturePrior indexed (headers := headers) (locations := locations)
          (expressionSyntax := expressionSyntax) (certificates := certificates) (registry := registry) (faults := faults)))
        formed.finalMap formed.finalWorld (FunctionValues.sourceType (head.formed environment)) (.closure formed.closure)
        (value (head.actualCode environment) formed.embedding (head.history entry environment).native formed.closureActual)
        (CallableContract.functionType (head.actualCode environment).receipt.parameterCore
          (head.actualCode environment).receipt.resultCore) := by
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation (captures complete globals entry related agrees typed)
    (head.actualCode environment) (head.history entry environment) head.snapshots
    (RecursiveNamedLambdaFormationHeads.LambdaWith.reference_index head) heaps
    (head.reference complete globals entry related agrees typed) entry.catalog.authority.frame.read
  exact ⟨formed, CallableIndexedLambdaRuntimeValues.formation_with indexed program formed (head.actualBody formed.captured)
    (formed_condition indexed head header complete globals slots entry related agrees typed checkedProgram formed)
    profile stored head.ordinary head.coercions⟩

include header slots profile stored heaps in
/-- The original native completion gives the same source formation, result,
and full store. The static predicate is built from the actual site again. -/
theorem reflects_original (checkedProgram : CheckedProgram) {result : Value} {after : Store}
    (completed : Evaluates actual store
      ((head.actualCode environment).lowered.expression.rename ξ) result after) :
    ∃ formed : Formed model (captures complete globals entry related agrees typed) (head.actualCode environment)
        (head.history entry environment) heap store entry.catalog.authority.frameLocation,
      result = .inRight .word (value (head.actualCode environment) formed.embedding (head.history entry environment).native
        formed.closureActual) ∧ after = formed.finalStore ∧
      Dynamic.ExpressionEvaluates program context evidence (head.formed environment).source environment heap
        (head.actualCode environment).id (.closure formed.closure) formed.finalHeap ∧
      RepresentsWith indexed (bodySupport indexed (expressionSyntax := expressionSyntax) (certificates := certificates)
          (program := program) (registry := registry) (faults := faults))
        (provenanceCondition indexed checkedProgram _ (capturePrior indexed (headers := headers) (locations := locations)
          (expressionSyntax := expressionSyntax) (certificates := certificates) (registry := registry) (faults := faults)))
        formed.finalMap formed.finalWorld (FunctionValues.sourceType (head.formed environment)) (.closure formed.closure)
        (value (head.actualCode environment) formed.embedding (head.history entry environment).native formed.closureActual)
        (CallableContract.functionType (head.actualCode environment).receipt.parameterCore
          (head.actualCode environment).receipt.resultCore) := by
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation (captures complete globals entry related agrees typed)
    (head.actualCode environment) (head.history entry environment) head.snapshots
    (RecursiveNamedLambdaFormationHeads.LambdaWith.reference_index head) heaps
    (head.reference complete globals entry related agrees typed) entry.catalog.authority.frame.read
  exact ⟨formed, CallableIndexedLambdaRuntimeValues.reflects_with indexed program formed (head.actualBody formed.captured)
    (formed_condition indexed head header complete globals slots entry related agrees typed checkedProgram formed)
    profile stored head.ordinary head.coercions completed⟩

end Formation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedStageOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedStageOrigins
/-! The existing nested-body model supplies function-leaf provenance from its
actual cached caller and same-Code static body. Its environments, heaps and
body meaning continue to use that identical model. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedStageOrigins
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaRuntimeValues
open CallableIndexedLambdaNestedRuntimeCertificates RecursiveNamedCatalog

variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
  {locations : Locations (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (program := program)}

/-- The stored caller is an actual cached header. The body supplies full source
identity and occurrence uniqueness independently of captured history. -/
theorem support_provenance {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    (body : CallableIndexedLambdaNestedRuntimeCertificates.Support (values := .initial compiled.compatible.checked) headers registry faults code) :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source ∧ NodeOccurrencesUnique function.source := by
  obtain ⟨caller, rank, body⟩ := body
  let receipt := body.receipt
  refine ⟨?_, receipt.body.unique⟩
  rw [receipt.compilation, receipt.active, receipt.source]
  exact .original (CallableIndexedActualNamedSourceReceipts.header_record compiled caller)

/-- A particular function leaf receives the source receipt established by its
own static support. No heap or function-model conversion is performed. -/
theorem origin_of_represents
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty}
    (related : (CallableIndexedLambdaNestedRuntimeCertificates.model (values := .initial compiled.compatible.checked) headers locations registry faults profile).Represents registry
      mapping world sourceType source carrier type) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table source carrier := by
  have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  cases related with
  | retained previous =>
    exact CallableIndexedStageOrigins.retained_origin (values := .initial compiled.compatible.checked) compiled.indexed prepared.accepted previous
  | lambda captured code history body supported typed =>
    have original := support_provenance (headers := headers) (registry := registry) (faults := faults) compiled body
    have provenance : CallableIndexedStageOrigins.provenanceCondition (values := .initial compiled.compatible.checked)
        compiled.indexed compiled.sourceProgram
        (CallableIndexedLambdaNestedRuntimeCertificates.Support (values := .initial compiled.compatible.checked) headers registry faults)
        (CallableIndexedLambdaNestedRuntimeCertificates.Condition (values := .initial compiled.compatible.checked) (registry := registry) (faults := faults) headers locations)
        captured code history body := ⟨supported, original⟩
    exact CallableIndexedStageOrigins.origin_of_represents (values := .initial compiled.compatible.checked) compiled.indexed
      (support := CallableIndexedLambdaNestedRuntimeCertificates.Support (values := .initial compiled.compatible.checked) headers registry faults) (prior := CallableIndexedLambdaNestedRuntimeCertificates.Condition (values := .initial compiled.compatible.checked) (registry := registry) (faults := faults) headers locations)
      prepared.accepted (RepresentsWith.lambda (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed) captured code history body provenance typed)

/-- Function origins are observations of the same nested model used by body
meaning. Actual sidecar and callsite equalities select its stage table. -/
theorem function_origins
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
    (samePlan : sidecar.plan = compiled.indexed.base.plan)
    (sameTable : site.table = compiled.indexed.ancestry.graph.inputs.callable.table) :
    CompatibleAmbientStageOrigins.FunctionOrigins
      (CallableIndexedLambdaNestedRuntimeCertificates.model (values := .initial compiled.compatible.checked) headers locations registry faults profile) registry sidecar site := by
  intro mapping world sourceType source carrier type related
  rw [samePlan, sameTable]
  exact origin_of_represents compiled profile related

private theorem callsite_table {table : SourceCoreStageCodebook.Table}
    {owner : SourceSpecialization.SpecializationKey} {call : ExpressionId}
    {reasonAt : SourceCoreCallableContracts.ReasonAt} {site : SourceCoreCallableContracts.Callsite}
    (issued : SourceCoreCallableContracts.prepareCallsite table owner call reasonAt = .ok site) :
    site.table = table := by
  unfold SourceCoreCallableContracts.prepareCallsite at issued
  split at issued
  · cases issued; rfl
  · cases issued

/-- All guard rows and function-leaf origins come from this actual compilation
and its existing nested model. The whole source and native heap stay unchanged. -/
theorem actual_compiled_coverage
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {context : SourceCoreFunctions.Context} {node : ExpressionNode} {callee : ExpressionId}
    {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {site : SourceCoreCallableContracts.Callsite} {sidecar : SourceCoreStageContracts.Sidecar}
    (issued : SourceCoreCallableContracts.prepareCallsite compiled.indexed.ancestry.graph.inputs.callable.table context.owner node.id
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.reasonAt = .ok site)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan context.owner = .ok sidecar)
    (contains : ContainsExpression sidecar.source node.id node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedLambdaNestedRuntimeCertificates.model (values := .initial compiled.compatible.checked) headers locations registry faults profile))
      (CallableLedger.frame sidecar) site node.id arguments sourceType type := by
  have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  intro mapping world source carrier contract represented bound
  exact CompatibleAmbientStageOrigins.actual_coverage prepared issued caller contains form
    (function_origins compiled profile (CallContractCertificates.sidecar_of_accepted caller).1
      (callsite_table issued)) sourceType type represented bound

/-- Callers recover the original captures, static body and capture condition.
The additional source attribution is derived from that exact stored body. -/
theorem closure_receipt
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {function : Dynamic.Closure} {native : Value} {type : Ty}
    (related : (CallableIndexedLambdaNestedRuntimeCertificates.model (values := .initial compiled.compatible.checked) headers locations registry faults profile).Represents registry
      mapping world sourceType (.closure function) native type) :
    ∃ scope actual, ∃ (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : CallableIndexedLambdaNestedRuntimeCertificates.Support (values := .initial compiled.compatible.checked) headers registry faults code),
      CallableIndexedLambdaNestedRuntimeCertificates.Condition (values := .initial compiled.compatible.checked) (registry := registry) (faults := faults) headers locations captured code history body ∧
      LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
        code.compilation.owner code.active function.source ∧ NodeOccurrencesUnique function.source ∧
      sourceType = FunctionValues.sourceType function ∧
      native = value code captured.embedding history.native actual ∧
      type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨scope, actual, captured, code, history, body, condition, sourceEq, nativeEq, typeEq⟩ :=
    RepresentsWith.closure_inv (values := .initial compiled.compatible.checked) compiled.indexed related
  obtain ⟨source, unique⟩ := support_provenance compiled body
  exact ⟨scope, actual, captured, code, history, body, condition, source, unique, sourceEq, nativeEq, typeEq⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedStageOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeEntry
/-! The reached lambda prefix keeps the actual installed catalog. Its source
allocation and native canonical spine transport the original global slots;
its protected store effects transport the original catalog authority after the
actual frame installation. No older lambda Entry or unused native environment
identity is needed, and no body execution law is stored in this adapter. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

section CatalogFor
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  {captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual}
  {code : Code prepared function scope captured.administrative} {history : History code}
  {inputs : CallableIndexedLambdaEntryPrefix.Context code} {functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared)}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame}
  (reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history inputs functions registry arguments before store location current)
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

/-- The input is an actual catalog observation at the original capture.
Only the original frame cell is installed, then the reached prefix's certified
effects and ordered canonical additions transport that observation. -/
def catalog_entry_for : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    reached.mapping reached.world reached.heap reached.store reached.canonical :=
  CallableIndexedLambdaCatalogEntries.catalog_entry_sized reached initial sameFrame

/-- This is the same physical frame cell as the one in the supplied original
catalog authority; it is not recovered from a native frame type. -/
theorem catalog_frame_for : (catalog_entry_for reached initial sameFrame).authority.frameLocation = location :=
  sameFrame

theorem catalog_current_for : (catalog_entry_for reached initial sameFrame).authority.current = reached.next := rfl

theorem catalog_ghost_for : (catalog_entry_for reached initial sameFrame).authority.ghost =
    .lambda code.descriptor.id history.ghost := rfl

include initial sameFrame in
/-- The actual reflected body's store effects compose with the original
prefix effects. Restoring the observed caller frame then transports the
original catalog Entry at its unchanged canonical capture. -/
theorem restore_catalog_for
    {finalMap : LocationMap} {finalWorld : StoreTyping} {after : Dynamic.Heap} {bodyStore : Store}
    {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
    (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
    (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions
      finalMap finalWorld after bodyStore)
    (maps : LocationMap.Extends reached.mapping finalMap)
    (worlds : WorldExtends reached.world finalWorld)
    (frame : AdministrativePreserved reached.mapping reached.store finalMap bodyStore)
    (metadata : Dynamic.HeapMetadataExtend reached.heap after) :
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) captured.canonical) ∧
    AdministrativePreserved mapping store finalMap
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) := by
  have unmapped : location ∉ mapping := sameFrame ▸ initial.authority.unmapped
  have typed : world[location]? = some prepared.ancestry.layout.frame.type := sameFrame ▸ initial.authority.typed
  obtain ⟨finalHeaps, restoredFrame, caller⟩ := CallableIndexedBodyFrames.restore
    (CallableIndexedAmbient.frame_registered prepared) unmapped typed
    (show CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
      location current currentGhost store from ⟨read, .stable currentCarried⟩)
    heaps (reached.worlds.trans worlds) (reached.frame.trans frame)
  exact ⟨finalHeaps, ⟨initial.extend (reached.maps.trans maps) (reached.worlds.trans worlds)
    restoredFrame (reached.metadata.trans metadata)⟩, restoredFrame, caller⟩

end CatalogFor

section ReflectionFor
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedLambdaRuntimeBody.Body code program registry faults)
  (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  (functionObservations : CompatibleEquality.FunctionObservations values.checked.catalog functions (Identity prepared))
  (functionViews : FunctionRuntimeViews functions)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

include body functions functionObservations functionViews extension uninitialized missing escaped initial sameFrame in
/-- The actual reached state consumes the canonical static receipt. Its builtin
children are closed by the runtime literal certificate at each reached site.
The original native body size is used directly; the source size is independent. -/
theorem reached_reflects_for [FunctionCalls.FaultTokens faults]
    (reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history body.toContext functions registry arguments before store location current)
    {size : Nat} {result : Value} {bodyStore : Store}
    (evaluated : EvaluationSize size reached.actual reached.store
      (code.receipt.body.rename reached.embedding) result bodyStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.context reached.environment reached.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after bodyStore ∧
      LocationMap.Extends reached.mapping finalMap ∧ WorldExtends reached.world finalWorld ∧
      AdministrativePreserved reached.mapping reached.store finalMap bodyStore ∧ Dynamic.HeapMetadataExtend reached.heap after := by
  let entry := RecursiveNamedCatalog.protectedEntry headers locations capturePrefix callerPrefix
  have expressionMeaning : ∀ context,
      CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence →
      RecursiveNamedBoundedContracts.Below size (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence
        function.source (CompatibleExpressionBuiltinRuntime.Certificate body.readFuel values function.source context
          code.compilation.solvedRequirements code.reasonAt) faults entry) := by
    intro context valid
    exact RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed entry
        (CompatibleExpressionBuiltinRuntime.reflects functions extension
          (identity_faithful prepared) functionObservations functionViews
          program function.evidence valid.ledger valid.runtime uninitialized missing)) size
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, _, _⟩ :=
    (CallableIndexedLambdaNamedRuntimeBodyMeaning.builtin_kernel code body).reflects_sized
      functions rfl (CallableIndexedAmbient.frame_registered prepared) extension program
      (identity_faithful prepared) functionObservations functionViews escaped
      (RecursiveNamedCatalog.entry_transport (headers := headers) (locations := locations))
      (RecursiveNamedCatalog.entry_binds (headers := headers) (locations := locations))
      (fun valid extended => valid.extend extended) (fun valid => valid)
      size size (Nat.le_refl size) expressionMeaning
      reached.environments reached.heaps reached.locals reached.lookups reached.actualTyped reached.reference
      reached.read reached.unmapped ⟨catalog_entry_for reached initial sameFrame⟩ evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata⟩


variable {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include body functions functionObservations functionViews extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The original application selects its actual reached prefix and strict
native body child. The independent source closure call uses that prefix's real
allocation and the same source frame; its source grade is separately retained.
Full store restoration then transports the original caller catalog Entry. -/
theorem reflects_original_for [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history body.toContext functions registry arguments before store location current,
      ∃ child bodyStore sourceSize outcome after finalMap finalWorld,
      child < size ∧ EvaluationSize child reached.actual reached.store
        (code.receipt.body.rename reached.embedding) result bodyStore ∧
      finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.context reached.environment reached.heap outcome after ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  have unmapped : location ∉ mapping := sameFrame ▸ initial.authority.unmapped
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    CallableIndexedLambdaEntryBounds.application_prefix_for captured code history body.toContext functions
      represented heaps locals reference read currentCarried unmapped allowed completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata⟩ :=
    reached_reflects_for captured code history body functions functionObservations functionViews extension uninitialized missing escaped initial sameFrame reached evaluated
  obtain ⟨restoredHeaps, restoredEntry, restoredFrame, caller⟩ :=
    restore_catalog_for reached initial sameFrame read currentCarried finalHeaps maps worlds frame metadata
  have source := trace.sound.call (context := callerContext) (caller := callerEvidence) body.frame body.extended reached.copy reached.allocation
  subst finalStore
  exact ⟨reached, child, bodyStore, sourceSize, outcome, after, finalMap, finalWorld,
    smaller, evaluated, rfl, trace, source, related, restoredHeaps, reached.maps.trans maps, reached.worlds.trans worlds,
    restoredFrame, reached.metadata.trans metadata, restoredEntry, caller⟩

include body functions functionObservations functionViews extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The public independent call outcome is a projection of the original sized
completion theorem. No older Entry agreement or preservation theorem is used. -/
theorem reflects_for [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨_, _, _, _, outcome, after, finalMap, finalWorld, _, _, _, _, source, rest⟩ :=
    reflects_original_for captured code history body functions functionObservations functionViews extension uninitialized missing escaped initial sameFrame
      represented heaps locals reference read currentCarried allowed completed
  exact ⟨outcome, after, finalMap, finalWorld, source, rest⟩

end ReflectionFor
section NamedReflection
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix : Nat}
  (body : CallableIndexedLambdaNamedRuntimeBodyMeaning.Body headers code program registry faults)
  (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  (functionObservations : CompatibleEquality.FunctionObservations values.checked.catalog functions (Identity prepared))
  (functionViews : FunctionRuntimeViews functions)
  (family : CallableIndexedLambdaNamedRuntimeBodyMeaning.CatalogFamily headers locations capturePrefix functions registry faults)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix code.compilation.administrativePrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

include body family functions functionObservations functionViews extension uninitialized missing escaped initial sameFrame in
theorem reached_reflects_named_for [FunctionCalls.FaultTokens faults]
    (reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history body.toContext functions registry arguments before store location current)
    {size : Nat} {result : Value} {bodyStore : Store}
    (evaluated : EvaluationSize size reached.actual reached.store
      (code.receipt.body.rename reached.embedding) result bodyStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.context reached.environment reached.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after bodyStore ∧
      LocationMap.Extends reached.mapping finalMap ∧ WorldExtends reached.world finalWorld ∧
      AdministrativePreserved reached.mapping reached.store finalMap bodyStore ∧ Dynamic.HeapMetadataExtend reached.heap after := by
  let installed := CallableIndexedLambdaCatalogEntries.source_entry_sized reached initial sameFrame
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, _⟩ :=
    CallableIndexedLambdaNamedRuntimeBodyMeaning.Body.reflects_sized code history body functions extension
      functionObservations functionViews family uninitialized missing escaped size size (Nat.le_refl size)
      reached.environments reached.heaps reached.locals reached.lookups reached.actualTyped reached.reference
      reached.read reached.unmapped ⟨installed⟩ evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata⟩


variable {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include body family functions functionObservations functionViews family extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The original application selects its actual reached prefix and strict
native body child. The independent source closure call uses that prefix's real
allocation and the same source frame; its source grade is separately retained.
Full store restoration then transports the original caller catalog Entry. -/
theorem reflects_original_named_for [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history body.toContext functions registry arguments before store location current,
      ∃ child bodyStore sourceSize outcome after finalMap finalWorld,
      child < size ∧ EvaluationSize child reached.actual reached.store
        (code.receipt.body.rename reached.embedding) result bodyStore ∧
      finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.context reached.environment reached.heap outcome after ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix code.compilation.administrativePrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  have unmapped : location ∉ mapping := sameFrame ▸ initial.authority.unmapped
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    CallableIndexedLambdaEntryBounds.application_prefix_for captured code history body.toContext functions
      represented heaps locals reference read currentCarried unmapped allowed completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata⟩ :=
    reached_reflects_named_for captured code history body functions functionObservations functionViews family extension uninitialized missing escaped initial sameFrame reached evaluated
  obtain ⟨restoredHeaps, restoredEntry, restoredFrame, caller⟩ :=
    restore_catalog_for reached initial sameFrame read currentCarried finalHeaps maps worlds frame metadata
  have source := trace.sound.call (context := callerContext) (caller := callerEvidence) body.frame body.extended reached.copy reached.allocation
  subst finalStore
  exact ⟨reached, child, bodyStore, sourceSize, outcome, after, finalMap, finalWorld,
    smaller, evaluated, rfl, trace, source, related, restoredHeaps, reached.maps.trans maps, reached.worlds.trans worlds,
    restoredFrame, reached.metadata.trans metadata, restoredEntry, caller⟩

include body family functions functionObservations functionViews family extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The public independent call outcome is a projection of the original sized
completion theorem. No older Entry agreement or preservation theorem is used. -/
theorem reflects_named_for [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix code.compilation.administrativePrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨_, _, _, _, outcome, after, finalMap, finalWorld, _, _, _, _, source, rest⟩ :=
    reflects_original_named_for captured code history body functions functionObservations functionViews family extension uninitialized missing escaped initial sameFrame
      represented heaps locals reference read currentCarried allowed completed
  exact ⟨outcome, after, finalMap, finalWorld, source, rest⟩

end NamedReflection

section NestedReflection
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {rank : Nat} {caller : RecursiveNamedCatalog.Header prepared.ancestry values prepared.layouts.definitions program}
  (body : CallableIndexedLambdaNestedRuntimeBodyMeaning.Body headers caller registry faults rank code)
  (profile : values.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions prepared) headers)
  (globals : caller.globals = prepared.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < prepared.base.globals.length)
  (metadataSource : history.metadata = CallableIndexedNamedGeneration.state caller.named)
  (family : CallableIndexedLambdaNamedRuntimeBodyMeaning.CatalogFamily headers locations 0 (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) registry faults)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame}
  (initial : RecursiveNamedCatalog.Entry headers locations 0 code.compilation.administrativePrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

include body complete globals slots metadataSource family extension uninitialized missing escaped initial sameFrame in
theorem reached_reflects_nested_for [FunctionCalls.FaultTokens faults]
    (reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history body.body.toContext (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) registry arguments before store location current)
    {size : Nat} {result : Value} {bodyStore : Store}
    (evaluated : EvaluationSize size reached.actual reached.store
      (code.receipt.body.rename reached.embedding) result bodyStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.body.context reached.environment reached.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) finalMap finalWorld after bodyStore ∧
      LocationMap.Extends reached.mapping finalMap ∧ WorldExtends reached.world finalWorld ∧
      AdministrativePreserved reached.mapping reached.store finalMap bodyStore ∧ Dynamic.HeapMetadataExtend reached.heap after := by
  let original := CallableIndexedLambdaCatalogEntries.source_entry_sized reached initial sameFrame
  let installed := CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.entry_of_source body original metadataSource globals reached.environments
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, _⟩ :=
    CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.reflects_sized code body profile complete globals slots extension
      family uninitialized missing escaped size size (Nat.le_refl size)
      reached.environments reached.heaps reached.locals reached.lookups reached.actualTyped reached.reference
      reached.read reached.unmapped ⟨installed⟩ evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata⟩


variable {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include body complete globals slots metadataSource family family extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The original application selects its actual reached prefix and strict
native body child. The independent source closure call uses that prefix's real
allocation and the same source frame; its source grade is separately retained.
Full store restoration then transports the original caller catalog Entry. -/
theorem reflects_original_nested_for [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history body.body.toContext (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) registry arguments before store location current,
      ∃ child bodyStore sourceSize outcome after finalMap finalWorld,
      child < size ∧ EvaluationSize child reached.actual reached.store
        (code.receipt.body.rename reached.embedding) result bodyStore ∧
      finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.body.context reached.environment reached.heap outcome after ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations 0 code.compilation.administrativePrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  have unmapped : location ∉ mapping := sameFrame ▸ initial.authority.unmapped
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    CallableIndexedLambdaEntryBounds.application_prefix_for captured code history body.body.toContext (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile)
      represented heaps locals reference read currentCarried unmapped allowed completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata⟩ :=
    reached_reflects_nested_for captured code history body profile complete globals slots metadataSource family extension uninitialized missing escaped initial sameFrame reached evaluated
  obtain ⟨restoredHeaps, restoredEntry, restoredFrame, caller⟩ :=
    restore_catalog_for reached initial sameFrame read currentCarried finalHeaps maps worlds frame metadata
  have source := trace.sound.call (context := callerContext) (caller := callerEvidence) body.body.frame body.body.extended reached.copy reached.allocation
  subst finalStore
  exact ⟨reached, child, bodyStore, sourceSize, outcome, after, finalMap, finalWorld,
    smaller, evaluated, rfl, trace, source, related, restoredHeaps, reached.maps.trans maps, reached.worlds.trans worlds,
    restoredFrame, reached.metadata.trans metadata, restoredEntry, caller⟩

include body complete globals slots metadataSource family family extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The public independent call outcome is a projection of the original sized
completion theorem. No older Entry agreement or preservation theorem is used. -/
theorem reflects_nested_for [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations 0 code.compilation.administrativePrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨_, _, _, _, outcome, after, finalMap, finalWorld, _, _, _, _, source, rest⟩ :=
    reflects_original_nested_for captured code history body profile complete globals slots metadataSource family extension uninitialized missing escaped initial sameFrame
      represented heaps locals reference read currentCarried allowed completed
  exact ⟨outcome, after, finalMap, finalWorld, source, rest⟩

end NestedReflection

section Catalog
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  {captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual}
  {code : Code prepared function scope captured.administrative} {history : History code}
  {inputs : CallableIndexedLambdaEntryPrefix.Context code} {profile : values.checked.catalog.callableContracts = true}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame}
  (reached : CallableIndexedLambdaEntryBounds.Prefix captured code history inputs profile registry arguments before store location current)
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

def catalog_entry : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    reached.mapping reached.world reached.heap reached.store reached.canonical := by
  exact catalog_entry_for reached.toFor initial sameFrame

theorem catalog_frame : (catalog_entry reached initial sameFrame).authority.frameLocation = location := by
  exact sameFrame

theorem catalog_current : (catalog_entry reached initial sameFrame).authority.current = reached.next := by
  rfl

theorem catalog_ghost : (catalog_entry reached initial sameFrame).authority.ghost =
    .lambda code.descriptor.id history.ghost := by
  rfl

include initial sameFrame in

theorem restore_catalog
    {finalMap : LocationMap} {finalWorld : StoreTyping} {after : Dynamic.Heap} {bodyStore : Store}
    {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
    (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
    (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile)
      finalMap finalWorld after bodyStore)
    (maps : LocationMap.Extends reached.mapping finalMap)
    (worlds : WorldExtends reached.world finalWorld)
    (frame : AdministrativePreserved reached.mapping reached.store finalMap bodyStore)
    (metadata : Dynamic.HeapMetadataExtend reached.heap after) :
    CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) captured.canonical) ∧
    AdministrativePreserved mapping store finalMap
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) := by
  exact restore_catalog_for reached.toFor initial sameFrame read currentCarried heaps maps worlds frame metadata

end Catalog

section Reflection
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedLambdaRuntimeBody.Body code program registry faults)
  (profile : values.checked.catalog.callableContracts = true)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

include body profile extension uninitialized missing escaped initial sameFrame in

theorem reached_reflects [FunctionCalls.FaultTokens faults]
    (reached : CallableIndexedLambdaEntryBounds.Prefix captured code history body.toContext profile registry arguments before store location current)
    {size : Nat} {result : Value} {bodyStore : Store}
    (evaluated : EvaluationSize size reached.actual reached.store
      (code.receipt.body.rename reached.embedding) result bodyStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.context reached.environment reached.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after bodyStore ∧
      LocationMap.Extends reached.mapping finalMap ∧ WorldExtends reached.world finalWorld ∧
      AdministrativePreserved reached.mapping reached.store finalMap bodyStore ∧ Dynamic.HeapMetadataExtend reached.heap after := by
  exact reached_reflects_for captured code history body (model prepared profile)
    (observations prepared profile) (runtime_views prepared profile) extension uninitialized missing escaped
    initial sameFrame reached.toFor evaluated

variable {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)


include body profile extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in

theorem reflects_original [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : CallableIndexedLambdaEntryBounds.Prefix captured code history body.toContext profile registry arguments before store location current,
      ∃ child bodyStore sourceSize outcome after finalMap finalWorld,
      child < size ∧ EvaluationSize child reached.actual reached.store
        (code.receipt.body.rename reached.embedding) result bodyStore ∧
      finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.context reached.environment reached.heap outcome after ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨reached, rest⟩ := reflects_original_for captured code history body (model prepared profile)
    (observations prepared profile) (runtime_views prepared profile) extension uninitialized missing escaped
    initial sameFrame represented heaps locals reference read currentCarried allowed completed
  exact ⟨reached.toLegacy (profile := profile), rest⟩

include body profile extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in

theorem reflects [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  exact reflects_for captured code history body (model prepared profile)
    (observations prepared profile) (runtime_views prepared profile) extension uninitialized missing escaped
    initial sameFrame represented heaps locals reference read currentCarried allowed completed

end Reflection



end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeEntry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimePreservation
/-! Independent source closure calls complete the actual indexed application.
The legacy builtin entry uses the shared finite body kernel with True entry.
NamedModel uses the same kernel and actual catalog/source prefix, with named
callee meaning closed by static profiles and the existing mutual induction.
Both restore the full caller catalog. Indirect apply, nested lambda formation
and general method body closure remain separate grammar boundaries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimePreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

private abbrev builtinEntry : ProtectedExpressionMeaning.Entry := fun _ _ _ _ _ _ => True
private theorem builtinTransport : ProtectedExpressionMeaning.Transport builtinEntry := ⟨fun _ _ _ _ _ => True.intro⟩
private theorem builtinBindings : ProtectedExpressionMeaning.Binds builtinEntry :=
  ⟨fun _ => True.intro, fun _ => True.intro⟩

section GeneralModel

variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedLambdaRuntimeBody.Body code program registry faults)
  (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions (Identity prepared))
  (functionTypes : FunctionRuntimeViews functions)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}

theorem wrap_body_at_for (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history inputs functions registry arguments nativeArguments before store location current currentGhost)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap} {result : Value} {bodyStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping}
    (evaluated : Evaluates entry.entry.actualBody entry.entry.store
      (code.receipt.body.rename entry.entry.embedding) result bodyStore)
    (related : FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result)
    (finalHeaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after bodyStore)
    (maps : LocationMap.Extends entry.entry.mapping finalMap) (worlds : WorldExtends entry.entry.world finalWorld)
    (frame : AdministrativePreserved entry.entry.mapping entry.entry.store finalMap bodyStore)
    (metadata : Dynamic.HeapMetadataExtend entry.entry.heap after) :
    Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    Dynamic.HeapMetadataExtend before after ∧
    CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) := by
  have applied : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result (bodyStore.set location (encode prepared.ancestry.layout.frame current)) :=
    .apply (.second (.first (.var rfl))) (.var rfl) (entry.wrap evaluated)
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ := CallableIndexedBodyFrames.restore
    (CallableIndexedAmbient.frame_registered prepared) entry.unmapped entry.referenceTyped
    (show CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
      location current currentGhost store from ⟨entry.currentRead, entry.currentHistory⟩)
    finalHeaps (entry.entry.worlds.trans worlds) (entry.entry.frame.trans frame)
  exact ⟨applied, related, restoredHeaps, entry.entry.maps.trans maps, entry.entry.worlds.trans worlds,
    restoredFrame, entry.entry.metadata.trans metadata, restoredCaller⟩

private theorem wrap_body_for (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history inputs functions registry arguments nativeArguments before store location current currentGhost)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap} {result : Value} {bodyStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping}
    (evaluated : Evaluates entry.entry.actualBody entry.entry.store
      (code.receipt.body.rename entry.entry.embedding) result bodyStore)
    (related : FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result)
    (finalHeaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after bodyStore)
    (maps : LocationMap.Extends entry.entry.mapping finalMap) (worlds : WorldExtends entry.entry.world finalWorld)
    (frame : AdministrativePreserved entry.entry.mapping entry.entry.store finalMap bodyStore)
    (metadata : Dynamic.HeapMetadataExtend entry.entry.heap after) :
    Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    Dynamic.HeapMetadataExtend before after ∧
    CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) :=
  wrap_body_at_for captured code history functions inputs entry evaluated related finalHeaps maps worlds frame metadata


include extension uninitialized missing escaped functionLeaves functionTypes in
/-- The independent source allocation is identified with this actual prefix.
The shared finite statement proof closes the body once; the real wrap then
completes the application and restores every unmapped caller cell. -/
theorem entry_preserves_for [FunctionCalls.FaultTokens faults]
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history body.toContext functions registry arguments nativeArguments before store location current currentGhost)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    {copies : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies function.source function.captured before copies copied)
    (allocated : Dynamic.BindersAllocate copies copied function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨sameCopies, sameCopied⟩ := Dynamic.EnvironmentCopies.functional entry.entry.copy copy
  rw [← sameCopies, ← sameCopied] at allocated
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  obtain ⟨size, sized⟩ := RecursiveNamedCallBounds.BodyTrace.has_size trace
  obtain ⟨result, bodyStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
    (CallableIndexedLambdaNamedRuntimeBodyMeaning.builtin_kernel code body).preserves_sized functions rfl
      (CallableIndexedAmbient.frame_registered prepared) extension program (identity_faithful prepared) functionLeaves escaped
      builtinTransport builtinBindings (fun valid extended => valid.extend extended) (fun valid => valid)
      size size (Nat.le_refl size)
      (fun context valid child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded
        (ProtectedExpressionMeaning.preserves_of_typed builtinEntry
          (CompatibleExpressionBuiltinRuntime.preserves functions extension
            (identity_faithful prepared) functionLeaves functionTypes
            program function.evidence valid.ledger valid.runtime body.unique uninitialized missing)) child)
      entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups
      entry.entry.actualTyped entry.entry.reference entry.entry.read entry.entry.unmapped True.intro sized
  exact ⟨result, _, finalMap, finalWorld,
    wrap_body_for captured code history functions body.toContext entry evaluated related finalHeaps maps worlds frame metadata⟩

variable {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include body extension uninitialized missing escaped functionLeaves functionTypes initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The source call supplies its own context, ordered allocation and body trace.
Only those static contexts and allocations are identified with the actual
prefix. The full original caller catalog is transported after restoration. -/
theorem preserves_for [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  have arity : function.parameters.length = arguments.length := by
    rw [CallableIndexedLambdaEntryPrefix.parameters code]
    simpa using represented.length.1
  obtain ⟨types, context, copies, copied, environment, bound, extended, copy, allocated, trace⟩ :=
    FunctionCallBody.Outcome.trace arity executed
  have sameTypes : types = body.types := extended.bodyTypes_eq.symm.trans body.extended.bodyTypes_eq
  subst types
  have sameContext := extended.functional body.extended
  subst context
  have unmapped : location ∉ mapping := sameFrame ▸ initial.authority.unmapped
  obtain ⟨entry⟩ := CallableIndexedLambdaEntryPrefix.entry_exists_for captured code history body.toContext functions
    represented heaps locals reference read currentCarried unmapped allowed
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, caller⟩ :=
    entry_preserves_for captured code history body functions functionLeaves functionTypes extension uninitialized missing escaped entry copy allocated trace
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata,
    ⟨initial.extend maps worlds frame metadata⟩, caller⟩

end GeneralModel

section NamedModel
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix : Nat}
  (body : CallableIndexedLambdaNamedRuntimeBodyMeaning.Body headers code program registry faults)
  (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions (Identity prepared))
  (functionTypes : FunctionRuntimeViews functions)
  (family : CallableIndexedLambdaNamedRuntimeBodyMeaning.CatalogFamily headers locations capturePrefix functions registry faults)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}

  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix code.compilation.administrativePrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

include body family owners extension uninitialized missing escaped functionLeaves functionTypes initial sameFrame in
/-- The actual ordered prefix retains its catalog source entry. The original
source child grade feeds the shared kernel, then the sole wrap/restore adapter
returns the complete caller store. -/
theorem entry_preserves_named_sized_for [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history body.toContext functions registry arguments nativeArguments before store location current currentGhost)
    {added copiedCanonical : Environment} (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ copiedCanonical)
    (kept : ∀ slot, scope.length ≤ slot → copiedCanonical[slot]? = captured.canonical[slot]?)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    {copies : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies function.source function.captured before copies copied)
    (allocated : Dynamic.BindersAllocate copies copied function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨sameCopies, sameCopied⟩ := Dynamic.EnvironmentCopies.functional entry.entry.copy copy
  rw [← sameCopies, ← sameCopied] at allocated
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  let installed := CallableIndexedLambdaCatalogEntries.source_entry entry initial sameFrame length spine kept
  obtain ⟨result, bodyStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    CallableIndexedLambdaNamedRuntimeBodyMeaning.Body.preserves_sized code history body functions extension functionLeaves
      functionTypes owners family uninitialized missing escaped budget size within
      entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups entry.entry.actualTyped
      entry.entry.reference entry.entry.read entry.entry.unmapped ⟨installed⟩ trace
  exact ⟨result, _, finalMap, finalWorld,
    wrap_body_for captured code history functions body.toContext entry evaluated related finalHeaps maps worlds frame metadata⟩

variable
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include body family owners extension uninitialized missing escaped functionLeaves functionTypes initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The original source body child supplies its grade independently of the
native application. Its actual prefix spine closes catalog installation and
full caller restoration without any unsized-to-sized conversion. -/
theorem preserves_named_sized_for [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {environment : Dynamic.Environment} {bound : Dynamic.Heap}
    {copies : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies function.source function.captured before copies copied)
    (allocated : Dynamic.BindersAllocate copies copied function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix code.compilation.administrativePrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  have unmapped : location ∉ mapping := sameFrame ▸ initial.authority.unmapped
  obtain ⟨entry, added, copiedCanonical, length, spine, kept⟩ := CallableIndexedLambdaEntryPrefix.entry_exists_for_with_spine
    captured code history body.toContext functions represented heaps locals reference read currentCarried unmapped allowed
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, caller⟩ :=
    entry_preserves_named_sized_for captured code history body functions functionLeaves functionTypes family owners extension
      uninitialized missing escaped initial sameFrame budget size within entry length spine kept copy allocated trace
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata,
    ⟨initial.extend maps worlds frame metadata⟩, caller⟩

end NamedModel

section NestedModel
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {rank : Nat} {caller : RecursiveNamedCatalog.Header prepared.ancestry values prepared.layouts.definitions program}
  (body : CallableIndexedLambdaNestedRuntimeBodyMeaning.Body headers caller registry faults rank code)
  (profile : values.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions prepared) headers)
  (globals : caller.globals = prepared.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < prepared.base.globals.length)
  (metadataSource : history.metadata = CallableIndexedNamedGeneration.state caller.named)
  (family : CallableIndexedLambdaNamedRuntimeBodyMeaning.CatalogFamily headers locations 0 (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) registry faults)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}

  (initial : RecursiveNamedCatalog.Entry headers locations 0 code.compilation.administrativePrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

include body complete globals slots metadataSource family owners extension uninitialized missing escaped initial sameFrame in
/-- The actual ordered prefix retains its catalog source entry. The original
source child grade feeds the shared kernel, then the sole wrap/restore adapter
returns the complete caller store. -/
theorem entry_preserves_nested_sized_for [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history body.body.toContext (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) registry arguments nativeArguments before store location current currentGhost)
    {added copiedCanonical : Environment} (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ copiedCanonical)
    (kept : ∀ slot, scope.length ≤ slot → copiedCanonical[slot]? = captured.canonical[slot]?)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    {copies : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies function.source function.captured before copies copied)
    (allocated : Dynamic.BindersAllocate copies copied function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function body.body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨sameCopies, sameCopied⟩ := Dynamic.EnvironmentCopies.functional entry.entry.copy copy
  rw [← sameCopies, ← sameCopied] at allocated
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  let original := CallableIndexedLambdaCatalogEntries.source_entry entry initial sameFrame length spine kept
  let installed := CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.entry_of_source body original metadataSource globals entry.entry.environments
  obtain ⟨result, bodyStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.preserves_sized code body profile complete globals slots extension family owners
      uninitialized missing escaped budget size within
      entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups entry.entry.actualTyped
      entry.entry.reference entry.entry.read entry.entry.unmapped ⟨installed⟩ trace
  exact ⟨result, _, finalMap, finalWorld,
    wrap_body_at_for captured code history (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) body.body.toContext entry evaluated related finalHeaps maps worlds frame metadata⟩

variable
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include body complete globals slots metadataSource family owners extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The original source body child supplies its grade independently of the
native application. Its actual prefix spine closes catalog installation and
full caller restoration without any unsized-to-sized conversion. -/
theorem preserves_nested_sized_for [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {environment : Dynamic.Environment} {bound : Dynamic.Heap}
    {copies : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies function.source function.captured before copies copied)
    (allocated : Dynamic.BindersAllocate copies copied function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function body.body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations 0 code.compilation.administrativePrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  have unmapped : location ∉ mapping := sameFrame ▸ initial.authority.unmapped
  obtain ⟨entry, added, copiedCanonical, length, spine, kept⟩ := CallableIndexedLambdaEntryPrefix.entry_exists_for_with_spine
    captured code history body.body.toContext (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) represented heaps locals reference read currentCarried unmapped allowed
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, caller⟩ :=
    entry_preserves_nested_sized_for captured code history body profile complete globals slots metadataSource family owners extension
      uninitialized missing escaped initial sameFrame budget size within entry length spine kept copy allocated trace
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata,
    ⟨initial.extend maps worlds frame metadata⟩, caller⟩

end NestedModel

variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedLambdaRuntimeBody.Body code program registry faults)
  (profile : values.checked.catalog.callableContracts = true)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}

include extension uninitialized missing escaped in
/-- The independent source allocation is identified with this actual prefix.
The shared finite statement proof closes the body once; the real wrap then
completes the application and restores every unmapped caller cell. -/
theorem entry_preserves [FunctionCalls.FaultTokens faults]
    (entry : CallableIndexedLambdaRuntimeBody.Entry captured code history body profile arguments nativeArguments before store location current currentGhost)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    {copies : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies function.source function.captured before copies copied)
    (allocated : Dynamic.BindersAllocate copies copied function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  exact entry_preserves_for captured code history body (model prepared profile)
    (observations prepared profile) (runtime_views prepared profile)
    extension uninitialized missing escaped entry.toFor copy allocated trace

variable {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include body extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The source call supplies its own context, ordered allocation and body trace.
Only those static contexts and allocations are identified with the actual
prefix. The full original caller catalog is transported after restoration. -/
theorem preserves [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  exact preserves_for captured code history body (model prepared profile)
    (observations prepared profile) (runtime_views prepared profile)
    extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed executed



end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimePreservation
end
