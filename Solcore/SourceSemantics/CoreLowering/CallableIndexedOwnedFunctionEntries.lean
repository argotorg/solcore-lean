import Solcore.SourceSemantics.CoreLowering.CallableIndexedAuthorityPool
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionValues

/-! Owned function values use actual selected pool rows as call-time catalogue
authority. Parameter prefixes retain all rows, complete captures and records.
Restoration installs the saved current into the reached pool, retaining records
accumulated in the body. No callable-body execution law is supplied here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog CallableIndexedAuthorityPool

section PoolAdapters

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program}
  {keys : List (Key prepared values ambient.definitions program)}
  {mapping futureMap finalMap : LocationMap} {world futureWorld finalWorld : StoreTyping}
  {heap after finalHeap : Dynamic.Heap} {store futureStore finalStore : Store}

/-- The immutable key position selects a live authority in this reached store. -/
def reached_authority (pool : Pool headers keys mapping world heap store)
    (selected : Fin keys.length) :
    Authority headers keys[selected.val].locations keys[selected.val].capturePrefix
      mapping world heap store :=
  (pool.rows selected).authority

theorem reached_frame_eq (pool : Pool headers keys mapping world heap store)
    (selected : Fin keys.length) :
    (reached_authority pool selected).frameLocation = keys[selected.val].frameLocation :=
  (pool.rows selected).frame_eq

theorem reached_frame_read (pool : Pool headers keys mapping world heap store)
    (selected : Fin keys.length) :
    store.read? keys[selected.val].frameLocation =
      some (encode prepared.layout.frame (pool.rows selected).authority.current) := by
  simpa only [(pool.rows selected).frame_eq] using (pool.rows selected).authority.frame.read

/-- Body records remain in the corresponding row; membership need not be
unique and the key domain is neither sorted nor deduplicated. -/
def RecordsExtend (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore) : Prop :=
  ∀ (i : Fin keys.length) record,
    record ∈ (saved.rows i).authority.records →
    record ∈ (reached.rows i).authority.records

theorem RecordsExtend.refl (pool : Pool headers keys mapping world heap store) :
    RecordsExtend pool pool := by
  intro i record member
  exact member

theorem RecordsExtend.trans
    {first : Pool headers keys mapping world heap store}
    {middle : Pool headers keys futureMap futureWorld after futureStore}
    {last : Pool headers keys finalMap finalWorld finalHeap finalStore}
    (left : RecordsExtend first middle) (right : RecordsExtend middle last) :
    RecordsExtend first last := by
  intro i record member
  exact right i record (left i record member)

theorem extend_records (pool : Pool headers keys mapping world heap store)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) (i : Fin keys.length) :
    ((pool.extend maps worlds frame metadata).rows i).authority.records =
      (pool.rows i).authority.records := rfl

theorem RecordsExtend.extend (pool : Pool headers keys mapping world heap store)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    RecordsExtend pool (pool.extend maps worlds frame metadata) := by
  intro i record member
  simpa only [extend_records] using member

theorem RecordsExtend.install (pool : Pool headers keys mapping world heap store)
    (selected : Fin keys.length) {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost) :
    RecordsExtend pool (pool.install selected history) := by
  intro i record member
  simpa only [Pool.install_records] using member

/-- The saved history is reinstalled in every reached row sharing this frame.
The reached rows, including their complete body records, remain the base pool. -/
def restored_pool (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected : Fin keys.length) :
    Pool headers keys futureMap futureWorld after
      (futureStore.set keys[selected.val].frameLocation
        (encode prepared.layout.frame (saved.rows selected).authority.current)) :=
  reached.install selected (saved.rows selected).authority.frame.history

theorem restored_records (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected i : Fin keys.length) :
    ((restored_pool saved reached selected).rows i).authority.records =
      (reached.rows i).authority.records :=
  Pool.install_records reached selected i (saved.rows selected).authority.frame.history

theorem RecordsExtend.restored
    (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected : Fin keys.length) (retained : RecordsExtend saved reached) :
    RecordsExtend saved (restored_pool saved reached selected) := by
  intro i record member
  simpa only [restored_records] using retained i record member

theorem restored_current (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected i : Fin keys.length) :
    ((restored_pool saved reached selected).rows i).authority.current =
      if keys[i.val].frameLocation = keys[selected.val].frameLocation
      then (saved.rows selected).authority.current else (reached.rows i).authority.current :=
  Pool.install_current reached selected i (saved.rows selected).authority.frame.history

theorem restored_ghost (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected i : Fin keys.length) :
    ((restored_pool saved reached selected).rows i).authority.ghost =
      if keys[i.val].frameLocation = keys[selected.val].frameLocation
      then (saved.rows selected).authority.ghost else (reached.rows i).authority.ghost :=
  Pool.install_ghost reached selected i (saved.rows selected).authority.frame.history

theorem restored_selected (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected : Fin keys.length) :
    ((restored_pool saved reached selected).rows selected).authority.current =
      (saved.rows selected).authority.current ∧
    ((restored_pool saved reached selected).rows selected).authority.ghost =
      (saved.rows selected).authority.ghost := by
  constructor
  · simpa using restored_current saved reached selected selected
  · simpa using restored_ghost saved reached selected selected

theorem restored_same_frame (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected i : Fin keys.length)
    (same : keys[i.val].frameLocation = keys[selected.val].frameLocation) :
    ((restored_pool saved reached selected).rows i).authority.current =
      (saved.rows selected).authority.current ∧
    ((restored_pool saved reached selected).rows i).authority.ghost =
      (saved.rows selected).authority.ghost := by
  constructor
  · simpa only [if_pos same] using restored_current saved reached selected i
  · simpa only [if_pos same] using restored_ghost saved reached selected i

theorem restored_other_frame (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected i : Fin keys.length)
    (different : keys[i.val].frameLocation ≠ keys[selected.val].frameLocation) :
    ((restored_pool saved reached selected).rows i).authority.current =
      (reached.rows i).authority.current ∧
    ((restored_pool saved reached selected).rows i).authority.ghost =
      (reached.rows i).authority.ghost := by
  constructor
  · simpa only [if_neg different] using restored_current saved reached selected i
  · simpa only [if_neg different] using restored_ghost saved reached selected i

/-- Every reached record retains its actual snapshot read, administrative
separation and carried metadata after restoration. -/
theorem restored_snapshot (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected i : Fin keys.length) {record : CallableIndexedSnapshots.Record}
    (member : record ∈ (reached.rows i).authority.records) :
    CallableIndexedSnapshots.Holds prepared.graph.inputs prepared.graph.table prepared.layout.frame
      futureMap (futureStore.set keys[selected.val].frameLocation
        (encode prepared.layout.frame (saved.rows selected).authority.current)) record := by
  apply ((restored_pool saved reached selected).rows i).authority.snapshots record
  simpa only [restored_records] using member

theorem restored_registered (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected : Fin keys.length) {record : CallableIndexedSnapshots.Record} :
    (restored_pool saved reached selected).Registered record ↔ reached.Registered record := by
  constructor
  · rintro ⟨i, member⟩
    exact ⟨i, by simpa only [restored_records] using member⟩
  · rintro ⟨i, member⟩
    exact ⟨i, by simpa only [restored_records] using member⟩

/-- The complete original capture, including any unused suffix, survives the
write at the selected frame. Different key location functions are permitted. -/
theorem restored_capture_read (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected i : Fin keys.length) {header : Header prepared values ambient.definitions program}
    (member : header ∈ headers)
    (capture : Capture headers keys[i.val].locations keys[i.val].capturePrefix
      (reached.rows i).authority.frameLocation header futureMap futureWorld after futureStore) :
    Store.read?
      (futureStore.set keys[selected.val].frameLocation
        (encode prepared.layout.frame (saved.rows selected).authority.current))
      (keys[i.val].locations header) =
      some (.inRight .unit (.closure header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename capture.embedding.lift) capture.captured)) :=
  Pool.install_capture_read reached selected i member capture

/-- Restore the actual saved cell once, then retain the reached pool by
installing the saved current/history into that pool. The returned cell uses
the key's physical location explicitly; no caller/callee frame equality is
introduced. All reached record lists and full capture reads are retained. -/
theorem restore_reached_pool
    (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected : Fin keys.length) {next : NativeFrame}
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    (registered : prepared.layout.frame.Registered ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions
      futureMap futureWorld after futureStore)
    (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping
      (store.set keys[selected.val].frameLocation (encode prepared.layout.frame next))
      futureMap futureStore) :
    ∃ finalPool : Pool headers keys futureMap futureWorld after
        (futureStore.set keys[selected.val].frameLocation
          (encode prepared.layout.frame (saved.rows selected).authority.current)),
      finalPool = restored_pool saved reached selected ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions
        futureMap futureWorld after
        (futureStore.set keys[selected.val].frameLocation
          (encode prepared.layout.frame (saved.rows selected).authority.current)) ∧
      AdministrativePreserved mapping store futureMap
        (futureStore.set keys[selected.val].frameLocation
          (encode prepared.layout.frame (saved.rows selected).authority.current)) ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame
        keys[selected.val].frameLocation (saved.rows selected).authority.current
        (saved.rows selected).authority.ghost
        (futureStore.set keys[selected.val].frameLocation
          (encode prepared.layout.frame (saved.rows selected).authority.current)) ∧
      (∀ i : Fin keys.length,
        (finalPool.rows i).authority.records = (reached.rows i).authority.records) ∧
      (∀ i : Fin keys.length,
        (finalPool.rows i).authority.current =
          if keys[i.val].frameLocation = keys[selected.val].frameLocation
          then (saved.rows selected).authority.current else (reached.rows i).authority.current) ∧
      (∀ i : Fin keys.length,
        (finalPool.rows i).authority.ghost =
          if keys[i.val].frameLocation = keys[selected.val].frameLocation
          then (saved.rows selected).authority.ghost else (reached.rows i).authority.ghost) ∧
      (∀ (i : Fin keys.length) (header : Header prepared values ambient.definitions program),
        header ∈ headers →
        ∀ capture : Capture headers keys[i.val].locations keys[i.val].capturePrefix
          (reached.rows i).authority.frameLocation header futureMap futureWorld after futureStore,
        Store.read?
          (futureStore.set keys[selected.val].frameLocation
            (encode prepared.layout.frame (saved.rows selected).authority.current))
          (keys[i.val].locations header) =
          some (.inRight .unit (.closure header.named.signature.parameterType
            (LanguageResult.resultType header.named.signature.resultType)
            (header.code.rename capture.embedding.lift) capture.captured))) := by
  let row := saved.rows selected
  obtain ⟨finalHeaps, restored, cell⟩ :=
    CallableIndexedBodyFrames.restore registered row.authority.unmapped row.authority.typed
      row.authority.frame heaps worlds (by simpa only [row.frame_eq] using frame)
  rw [row.frame_eq] at finalHeaps restored cell
  refine ⟨restored_pool saved reached selected, rfl, finalHeaps, restored, cell, ?_, ?_, ?_, ?_⟩
  · exact fun i => restored_records saved reached selected i
  · exact fun i => restored_current saved reached selected i
  · exact fun i => restored_ghost saved reached selected i
  · exact fun i header member capture => restored_capture_read saved reached selected i member capture

end PoolAdapters

open CallableIndexedOwnedFunctionValues (OwnedKey NamedCapture)

/-- The fixed owned-key domain uses the same prepared compilation and full
initial values context as the owned function relation. -/
abbrev OwnedPool {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program))
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) :=
  Pool (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers keys mapping world heap store

section OwnedCaptures

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

/-- The immutable owner selects an actual full capture in this reached pool.
Its physical frame is transported through the row's explicit equality. -/
theorem capture_from_pool (pool : OwnedPool headers keys mapping world heap store)
    (owner : OwnedKey keys) {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (member : header ∈ headers) :
    Nonempty (Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix owner.key.frameLocation
      header mapping world heap store) := by
  obtain ⟨capture⟩ := (pool.rows owner.position).authority.captures header member
  have same := (pool.rows owner.position).frame_eq
  change (pool.rows owner.position).authority.frameLocation = owner.key.frameLocation at same
  rw [same] at capture
  exact ⟨capture⟩

/-- Store-independent named evidence becomes a live capture only with the
exact closure read. Local agreement and administrative separation are taken
from the actual same-header row, retaining all captured values. -/
def named_capture_reached (pool : OwnedPool headers keys mapping world heap store)
    (owner : OwnedKey keys) {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (member : header ∈ headers) (capture : NamedCapture headers owner.key header mapping world)
    (read : store.read? (owner.key.locations header) = some (.inRight .unit
      (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename capture.embedding.lift) capture.captured))) :
    Capture (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix owner.key.frameLocation
      header mapping world heap store := by
  have live : Dynamic.EnvironmentAgrees heap header.function.context.locals [] ∧
      owner.key.locations header ∉ mapping ∧ owner.key.locations header ≠ owner.key.frameLocation := by
    obtain ⟨original⟩ := capture_from_pool pool owner member
    exact ⟨original.locals, original.unmapped, original.distinct⟩
  exact {
    administrative := capture.administrative
    canonical := capture.canonical
    captured := capture.captured
    capturedContext := capture.capturedContext
    embedding := capture.embedding
    environments := capture.environments
    locals := live.1
    layout := capture.layout
    typed := capture.typed
    reference := capture.reference
    capturedReference := capture.capturedReference
    coherent := capture.coherent
    unmapped := live.2.1
    distinct := live.2.2
    read := read }

theorem named_capture_reached_embedding
    (pool : OwnedPool headers keys mapping world heap store) (owner : OwnedKey keys)
    {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers)
    (capture : NamedCapture headers owner.key header mapping world)
    (read : store.read? (owner.key.locations header) = some (.inRight .unit
      (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename capture.embedding.lift) capture.captured))) :
    (named_capture_reached pool owner member capture read).embedding = capture.embedding := by
  unfold named_capture_reached
  rfl

theorem named_capture_reached_captured
    (pool : OwnedPool headers keys mapping world heap store) (owner : OwnedKey keys)
    {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers)
    (capture : NamedCapture headers owner.key header mapping world)
    (read : store.read? (owner.key.locations header) = some (.inRight .unit
      (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename capture.embedding.lift) capture.captured))) :
    (named_capture_reached pool owner member capture read).captured = capture.captured := by
  unfold named_capture_reached
  rfl

variable {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}

/-- Actual canonical global/frame observations select the same owner row.
The key's complete capture prefix is retained without requiring an empty
catalogue or equality to another caller's physical frame. -/
def initial_catalog (pool : OwnedPool headers keys mapping world heap store)
    (owner : OwnedKey keys)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations callerPrefix scope canonical owner.key.frameLocation) :
    RecursiveNamedCatalog.Entry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix callerPrefix scope
      mapping world heap store canonical :=
  globals.catalog (pool.rows owner.position).authority

theorem initial_catalog_frame_eq (pool : OwnedPool headers keys mapping world heap store)
    (owner : OwnedKey keys)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations callerPrefix scope canonical owner.key.frameLocation) :
    (initial_catalog pool owner globals).authority.frameLocation = owner.key.frameLocation :=
  (pool.rows owner.position).frame_eq

end OwnedCaptures

section NamedParameters

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {payloads : List Value}
  {actual : Environment} {actualContext : Core.Context} {xi : Renaming}

/-- Named parameter allocation uses the represented value's original full
canonical layout. Independent live authority supplies only its actual frame
and source local agreement; no different catalogue payload is substituted. -/
theorem named_parameters (pool : OwnedPool headers keys mapping world heap store)
    (owner : OwnedKey keys) (member : header ∈ headers)
    (capture : NamedCapture headers owner.key header mapping world)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
      registry functions mapping world heap store)
    (agrees : EnvironmentsAgree xi (DataPatternValues.packValues payloads :: capture.canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions) :
    Nonempty (RecursiveNamedCatalog.ParameterEntry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual xi owner.key.frameLocation
      (pool.rows owner.position).authority.current (pool.rows owner.position).authority.ghost) := by
  have locals : Dynamic.EnvironmentAgrees heap header.function.context.locals [] := by
    obtain ⟨original⟩ := capture_from_pool pool owner member
    exact original.locals
  have physical : (pool.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
    (pool.rows owner.position).frame_eq
  have reference : capture.canonical[header.globals]? = some
      (.cellRef compiled.indexed.ancestry.layout.frame.type (pool.rows owner.position).authority.frameLocation) := by
    exact capture.reference.trans (congrArg
      (fun location => some (Value.cellRef compiled.indexed.ancestry.layout.frame.type location)) physical.symm)
  have produced := RecursiveNamedCatalog.parameters_of_layout (pool.rows owner.position).authority
    capture.environments locals reference capture.coherent represented heaps agrees actualTyped
  exact Eq.mp (congrArg (fun location =>
    Nonempty (RecursiveNamedCatalog.ParameterEntry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual xi location
      (pool.rows owner.position).authority.current (pool.rows owner.position).authority.ghost)) physical) produced

variable (pool : OwnedPool headers keys mapping world heap store) (owner : OwnedKey keys)
  (capture : NamedCapture headers owner.key header mapping world)
  (entry : RecursiveNamedCatalog.ParameterEntry (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap store mapping world
    capture.administrative actualContext actual xi owner.key.frameLocation
    (pool.rows owner.position).authority.current (pool.rows owner.position).authority.ghost)

/-- The actual parameter prefix transports every pool row and its complete
records through its certified maps, worlds, frame and source metadata. -/
def named_parameter_pool : OwnedPool headers keys entry.mapping entry.world entry.heap entry.store :=
  pool.extend entry.maps entry.worlds entry.frame entry.metadata

theorem named_parameter_pool_records (i : Fin keys.length) :
    ((named_parameter_pool pool owner capture entry).rows i).authority.records =
      (pool.rows i).authority.records := rfl

theorem named_parameter_pool_current (i : Fin keys.length) :
    ((named_parameter_pool pool owner capture entry).rows i).authority.current =
      (pool.rows i).authority.current := rfl

theorem named_parameter_pool_ghost (i : Fin keys.length) :
    ((named_parameter_pool pool owner capture entry).rows i).authority.ghost =
      (pool.rows i).authority.ghost := rfl

theorem named_parameter_catalog_current :
    entry.catalog.authority.current =
      ((named_parameter_pool pool owner capture entry).rows owner.position).authority.current :=
  entry.catalog_current

theorem named_parameter_catalog_ghost :
    entry.catalog.authority.ghost =
      ((named_parameter_pool pool owner capture entry).rows owner.position).authority.ghost :=
  entry.catalog_ghost

theorem named_parameter_catalog_frame_eq :
    entry.catalog.authority.frameLocation = owner.key.frameLocation :=
  entry.catalog_frame

/-- The actual prefix's observed global slots can be paired with the selected
reached pool authority. This entry retains the pool's exact records rather
than asserting equality for an arbitrary ParameterEntry's catalogue. -/
def named_parameter_catalog :
    RecursiveNamedCatalog.Entry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix (owner.key.capturePrefix + 1)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entry.mapping entry.world entry.heap entry.store entry.canonical :=
  ⟨((named_parameter_pool pool owner capture entry).rows owner.position).authority, entry.catalog.globals⟩

theorem named_parameter_catalog_records :
    (named_parameter_catalog pool owner capture entry).authority.records =
      ((named_parameter_pool pool owner capture entry).rows owner.position).authority.records := rfl

theorem named_parameter_catalog_owner_frame :
    (named_parameter_catalog pool owner capture entry).authority.frameLocation = owner.key.frameLocation :=
  ((named_parameter_pool pool owner capture entry).rows owner.position).frame_eq

end NamedParameters

section OrdinaryPrefix

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {capturedActual : Environment}
  {captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world scope function.captured capturedActual}
  {code : CallableIndexedLambdaValues.Code compiled.indexed function scope captured.administrative}
  {history : CallableIndexedLambdaValues.History code}
  {inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (pool : OwnedPool headers keys mapping world heap store) (owner : OwnedKey keys)
  (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
    captured code history inputs functions registry arguments nativeArguments heap store owner.key.frameLocation
    (pool.rows owner.position).authority.current (pool.rows owner.position).authority.ghost)

/-- The actual ordinary prefix installs its stable lambda history in all
rows sharing the physical frame, then transports the complete pool through
its real allocation effects. The function model remains arbitrary. -/
def ordinary_pool : OwnedPool headers keys entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store :=
  (pool.install owner.position (Current.stable entry.nextHistory)).extend
    entry.entry.maps entry.entry.worlds entry.entry.frame entry.entry.metadata

theorem ordinary_pool_records (i : Fin keys.length) :
    ((ordinary_pool pool owner entry).rows i).authority.records = (pool.rows i).authority.records :=
  Pool.install_records pool owner.position i (Current.stable entry.nextHistory)

theorem ordinary_pool_current (i : Fin keys.length) :
    ((ordinary_pool pool owner entry).rows i).authority.current =
      if keys[i.val].frameLocation = owner.key.frameLocation then entry.next
      else (pool.rows i).authority.current :=
  Pool.install_current pool owner.position i (Current.stable entry.nextHistory)

theorem ordinary_pool_ghost (i : Fin keys.length) :
    ((ordinary_pool pool owner entry).rows i).authority.ghost =
      if keys[i.val].frameLocation = owner.key.frameLocation then .lambda code.descriptor.id history.ghost
      else (pool.rows i).authority.ghost :=
  Pool.install_ghost pool owner.position i (Current.stable entry.nextHistory)

variable {callerPrefix : Nat}
  (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
  {added : Environment} (length : added.length = code.receipt.loweredParameters.length)
  (spine : entry.entry.canonical = added ++ captured.canonical)

/-- The source entry comes from the same unsized prefix and its retained
ordered spine. The lambda ghost and full carried metadata are unchanged. -/
def ordinary_source_entry :
    CallableIndexedLambdaCatalogEntries.SourceEntry (values := .initial compiled.compatible.checked)
      code history headers owner.key.locations owner.key.capturePrefix callerPrefix
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store entry.entry.canonical :=
  CallableIndexedLambdaCatalogEntries.source_entry entry (initial_catalog pool owner globals)
    (initial_catalog_frame_eq pool owner globals) length spine

theorem ordinary_source_entry_frame_eq :
    (ordinary_source_entry pool owner entry globals length spine).catalog.authority.frameLocation =
      owner.key.frameLocation :=
  initial_catalog_frame_eq pool owner globals

/-- The selected source-entry row and the transported pool retain the exact
same record list. This comparison concerns authority data, not proof terms. -/
theorem ordinary_source_entry_records :
    (ordinary_source_entry pool owner entry globals length spine).catalog.authority.records =
      ((ordinary_pool pool owner entry).rows owner.position).authority.records :=
  (ordinary_pool_records pool owner entry owner.position).symm

theorem ordinary_source_entry_current :
    (ordinary_source_entry pool owner entry globals length spine).catalog.authority.current =
      ((ordinary_pool pool owner entry).rows owner.position).authority.current := by
  change entry.next = ((ordinary_pool pool owner entry).rows owner.position).authority.current
  have same := ordinary_pool_current pool owner entry owner.position
  simpa [CallableIndexedOwnedFunctionValues.OwnedKey.key] using same.symm

theorem ordinary_source_entry_ghost :
    (ordinary_source_entry pool owner entry globals length spine).catalog.authority.ghost =
      ((ordinary_pool pool owner entry).rows owner.position).authority.ghost := by
  change (SourceCoreCallablePairedFrames.Frame.lambda code.descriptor.id history.ghost) =
    ((ordinary_pool pool owner entry).rows owner.position).authority.ghost
  have same := ordinary_pool_ghost pool owner entry owner.position
  simpa [CallableIndexedOwnedFunctionValues.OwnedKey.key] using same.symm

end OrdinaryPrefix

section OrdinarySizedPrefix

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {capturedActual : Environment}
  {captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world scope function.captured capturedActual}
  {code : CallableIndexedLambdaValues.Code compiled.indexed function scope captured.administrative}
  {history : CallableIndexedLambdaValues.History code}
  {inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value}
  (pool : OwnedPool headers keys mapping world heap store) (owner : OwnedKey keys)
  (reached : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
    captured code history inputs functions registry arguments heap store owner.key.frameLocation
    (pool.rows owner.position).authority.current)

/-- Reflection uses the actual sized prefix's effects and history. Original
Core body grades remain in that prefix and are not manufactured here. -/
def ordinary_pool_sized : OwnedPool headers keys reached.mapping reached.world reached.heap reached.store :=
  (pool.install owner.position (Current.stable reached.nextHistory)).extend
    reached.maps reached.worlds reached.frame reached.metadata

theorem ordinary_pool_sized_records (i : Fin keys.length) :
    ((ordinary_pool_sized pool owner reached).rows i).authority.records = (pool.rows i).authority.records :=
  Pool.install_records pool owner.position i (Current.stable reached.nextHistory)

theorem ordinary_pool_sized_current (i : Fin keys.length) :
    ((ordinary_pool_sized pool owner reached).rows i).authority.current =
      if keys[i.val].frameLocation = owner.key.frameLocation then reached.next
      else (pool.rows i).authority.current :=
  Pool.install_current pool owner.position i (Current.stable reached.nextHistory)

theorem ordinary_pool_sized_ghost (i : Fin keys.length) :
    ((ordinary_pool_sized pool owner reached).rows i).authority.ghost =
      if keys[i.val].frameLocation = owner.key.frameLocation then .lambda code.descriptor.id history.ghost
      else (pool.rows i).authority.ghost :=
  Pool.install_ghost pool owner.position i (Current.stable reached.nextHistory)

variable {callerPrefix : Nat}
  (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)

def ordinary_source_entry_sized :
    CallableIndexedLambdaCatalogEntries.SourceEntry (values := .initial compiled.compatible.checked)
      code history headers owner.key.locations owner.key.capturePrefix callerPrefix
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      reached.mapping reached.world reached.heap reached.store reached.canonical :=
  CallableIndexedLambdaCatalogEntries.source_entry_sized reached (initial_catalog pool owner globals)
    (initial_catalog_frame_eq pool owner globals)

theorem ordinary_source_entry_sized_frame_eq :
    (ordinary_source_entry_sized pool owner reached globals).catalog.authority.frameLocation =
      owner.key.frameLocation :=
  initial_catalog_frame_eq pool owner globals

theorem ordinary_source_entry_sized_records :
    (ordinary_source_entry_sized pool owner reached globals).catalog.authority.records =
      ((ordinary_pool_sized pool owner reached).rows owner.position).authority.records :=
  (ordinary_pool_sized_records pool owner reached owner.position).symm

theorem ordinary_source_entry_sized_current :
    (ordinary_source_entry_sized pool owner reached globals).catalog.authority.current =
      ((ordinary_pool_sized pool owner reached).rows owner.position).authority.current := by
  change reached.next = ((ordinary_pool_sized pool owner reached).rows owner.position).authority.current
  have same := ordinary_pool_sized_current pool owner reached owner.position
  simpa [CallableIndexedOwnedFunctionValues.OwnedKey.key] using same.symm

theorem ordinary_source_entry_sized_ghost :
    (ordinary_source_entry_sized pool owner reached globals).catalog.authority.ghost =
      ((ordinary_pool_sized pool owner reached).rows owner.position).authority.ghost := by
  change (SourceCoreCallablePairedFrames.Frame.lambda code.descriptor.id history.ghost) =
    ((ordinary_pool_sized pool owner reached).rows owner.position).authority.ghost
  have same := ordinary_pool_sized_ghost pool owner reached owner.position
  simpa [CallableIndexedOwnedFunctionValues.OwnedKey.key] using same.symm

end OrdinarySizedPrefix

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionEntries
