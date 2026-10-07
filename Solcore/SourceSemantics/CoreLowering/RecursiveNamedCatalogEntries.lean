import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterTyped
import Solcore.SourceSemantics.CoreLowering.CallableIndexedBodyFrames
import Solcore.SourceSemantics.CoreLowering.CallableIndexedFormation
import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionBindings

/-! Shared physical global references connect each actual captured environment
to the complete finite catalog. Named installation and the real marked
parameter capturePrefix retain that catalog; restoration uses actual administrative
preservation. Neither typing nor heap correspondence creates this authority. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}

abbrev Locations := Header prepared values ambient.definitions program → Location

/-- Every row retains its real captured code and references. Coherence is an
explicit observation of all shared global locations in its canonical capture
layout, independent of the caller's lexical environment. -/
structure Capture (headers : Inventory prepared values ambient.definitions program)
    (locations : Locations) (capturePrefix : Nat) (frameLocation : Location)
    (header : Header prepared values ambient.definitions program)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  administrative : Core.Context
  canonical : Environment
  captured : Environment
  capturedContext : Core.Context
  embedding : Renaming
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
    mapping world administrative [] [] canonical ambient.definitions
  locals : Dynamic.EnvironmentAgrees heap header.function.context.locals []
  layout : EnvironmentsAgree embedding canonical captured
  typed : RuntimeEnvironmentHasTypes world captured capturedContext ambient.definitions
  reference : canonical[header.globals]? = some (.cellRef prepared.layout.frame.type frameLocation)
  capturedReference : captured[embedding base.globals.length]? = some (.cellRef prepared.layout.frame.type frameLocation)
  coherent : ∀ target, target ∈ headers → canonical[capturePrefix + target.slot]? = some
    (.cellRef (OptionalCell.cellType target.named.signature.functionType) (locations target))
  unmapped : locations header ∉ mapping
  distinct : locations header ≠ frameLocation
  read : store.read? (locations header) = some (.inRight .unit
    (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
      (header.code.rename embedding.lift) captured))

/-- Current frame history and all exact closures share one physical frame cell.
The frame snapshots are distinct protected cells. -/
structure Authority (headers : Inventory prepared values ambient.definitions program)
    (locations : Locations) (capturePrefix : Nat) (mapping : LocationMap) (world : StoreTyping)
    (heap : Dynamic.Heap) (store : Store) where
  frameLocation : Location
  unmapped : frameLocation ∉ mapping
  typed : world[frameLocation]? = some prepared.layout.frame.type
  current : NativeFrame
  ghost : GhostFrame
  frame : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame frameLocation current ghost store
  records : List CallableIndexedSnapshots.Record
  snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records
  distinct : ∀ record, record ∈ records → record.location ≠ frameLocation
  captures : ∀ header, header ∈ headers → Nonempty (Capture headers locations capturePrefix frameLocation header mapping world heap store)

structure Entry (headers : Inventory prepared values ambient.definitions program)
    (locations : Locations) (capturePrefix callerPrefix : Nat) (scope : Scope)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (canonical : Environment) where
  authority : Authority headers locations capturePrefix mapping world heap store
  globals : ∀ header, header ∈ headers → canonical[scope.length + callerPrefix + header.slot]? = some
    (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header))

variable {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix callerPrefix : Nat} {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
  {heap after : Dynamic.Heap} {store futureStore : Store} {location : Location}

/-- Actual administrative preservation transports every retained closure.
Its captured values and code are unchanged; only typing and source metadata
are weakened along the certified extensions. -/
def Capture.extend {header : Header prepared values ambient.definitions program}
    (capture : Capture headers locations capturePrefix location header mapping world heap store)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Capture headers locations capturePrefix location header futureMap futureWorld after futureStore := by
  have retained :=  frame (locations header) capture.unmapped (List.getElem?_eq_some_iff.mp capture.read).1
  exact { capture with
    environments := capture.environments.extend maps worlds
    locals := capture.locals.mono metadata
    typed := capture.typed.weaken worlds
    unmapped := retained.1
    read := retained.2.trans capture.read }

def Authority.extend (authority : Authority headers locations capturePrefix mapping world heap store)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Authority headers locations capturePrefix futureMap futureWorld after futureStore := by
  have retained :=  frame authority.frameLocation authority.unmapped (List.getElem?_eq_some_iff.mp authority.frame.read).1
  refine { authority with
    unmapped := retained.1
    typed := worlds.lookup authority.typed
    frame := ⟨retained.2.trans authority.frame.read, authority.frame.history⟩
    snapshots := authority.snapshots.transport frame
    captures := ?_ }
  intro header member
  obtain ⟨capture⟩ := authority.captures header member
  exact ⟨capture.extend maps worlds frame metadata⟩

def Entry.extend {scope : Scope} {canonical : Environment}
    (entry : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Entry headers locations capturePrefix callerPrefix scope futureMap futureWorld after futureStore canonical :=
  ⟨entry.authority.extend maps worlds frame metadata, entry.globals⟩

/-- Installing a named frame changes only the shared frame cell. Actual global
closure cells and protected snapshots are distinct, so their reads survive. -/
def Authority.install (authority : Authority headers locations capturePrefix mapping world heap store)
    {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost) :
    Authority headers locations capturePrefix mapping world heap
      (store.set authority.frameLocation (encode prepared.layout.frame next)) := by
  have written : store.write? authority.frameLocation (encode prepared.layout.frame next) =
      some (store.set authority.frameLocation (encode prepared.layout.frame next)) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp authority.frame.read).1, rfl⟩
  refine { authority with
    current := next
    ghost := nextGhost
    frame := ⟨Store.write?_reads_written written, history⟩
    snapshots := CallableIndexedBodyFrames.install_snapshots authority.frame authority.snapshots authority.distinct
    captures := ?_ }
  intro header member
  obtain ⟨capture⟩ := authority.captures header member
  exact ⟨{ capture with read := (Store.write?_preserves_other written capture.distinct).trans capture.read }⟩

/-- The actual hook receipt fixes the named history and emitted wrapper. The
callee's full catalog comes from its observed capture coherence, rather than
from its source or native type. -/
theorem named_install (authority : Authority headers locations capturePrefix mapping world heap store)
    {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store) :
    ∃ origin index metadata,
      prepared.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      header.code = withFrame (.var (base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) header.parameterCode ∧
      ∃ capture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap store,
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap
          (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) ∧
        Nonempty (Entry headers locations capturePrefix capturePrefix [] mapping world heap
          (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) capture.canonical) := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared header.hook
  obtain ⟨capture⟩ := authority.captures header member
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  exact ⟨origin, index, metadata, owned, history, emitted, capture, installedHeaps,
    ⟨authority.install (.stable history), by simpa using capture.coherent⟩⟩

/-- Restoration consumes the actual child frame relation. It recovers the
original caller authority for every catalog row and snapshot, with final source
heap effects retained. No child body execution is assumed here. -/
theorem restore {scope : Scope} {canonical : Environment}
    (entry : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    {next : NativeFrame} {functions : FunctionModel values.checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry}
    (registered : prepared.layout.frame.Registered ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after futureStore)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping
      (store.set entry.authority.frameLocation (encode prepared.layout.frame next)) futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after
      (futureStore.set entry.authority.frameLocation (encode prepared.layout.frame entry.authority.current)) ∧
    Nonempty (Authority headers locations capturePrefix futureMap futureWorld after
      (futureStore.set entry.authority.frameLocation (encode prepared.layout.frame entry.authority.current))) := by
  obtain ⟨finalHeaps, restored, _⟩ := CallableIndexedBodyFrames.restore registered entry.authority.unmapped entry.authority.typed
    entry.authority.frame heaps worlds frame
  exact ⟨finalHeaps, ⟨entry.authority.extend maps worlds restored metadata⟩⟩

/-- Lookup of an actual installed target returns precisely its retained
closure, without executing any target body. -/
theorem Entry.read_target {scope : Scope} {canonical actual : Environment} {ξ : Renaming}
    (entry : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {header : Header prepared values ambient.definitions program} (member : header ∈ headers) (reason : Word) :
    ∃ capture : Capture headers locations capturePrefix entry.authority.frameLocation header mapping world heap store,
      Evaluates actual store (OptionalCell.read header.named.signature.functionType
        (.var (ξ (scope.length + callerPrefix + header.slot))) reason)
        (.inRight .word (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured)) store := by
  obtain ⟨capture⟩ := entry.authority.captures header member
  exact ⟨capture, OptionalCell.read_success reason (.var (agrees (entry.globals header member))) capture.read⟩

/-- Each captured global points to the same physical location as the caller's
catalog. This is obtained only from the stored coherence receipt. -/
theorem Capture.global_reference {header : Header prepared values ambient.definitions program}
    (capture : Capture headers locations capturePrefix location header mapping world heap store)
    {target : Header prepared values ambient.definitions program} (member : target ∈ headers) :
    capture.captured[capture.embedding (capturePrefix + target.slot)]? = some
      (.cellRef (OptionalCell.cellType target.named.signature.functionType) (locations target)) :=
  capture.layout (capture.coherent target member)

def protectedEntry (headers : Inventory prepared values ambient.definitions program)
    (locations : Header prepared values ambient.definitions program → Location) (capturePrefix callerPrefix : Nat) : ProtectedExpressionMeaning.Entry :=
  fun scope mapping world heap store canonical =>
    Nonempty (Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)

theorem entry_transport : ProtectedExpressionMeaning.Transport
    (protectedEntry headers locations capturePrefix callerPrefix) := by
  constructor
  intro scope mapping world heap store canonical futureMap futureWorld after futureStore entry maps worlds frame metadata
  obtain ⟨entry⟩ := entry
  exact ⟨entry.extend maps worlds frame metadata⟩

theorem entry_binds : ProtectedExpressionMeaning.Binds
    (protectedEntry headers locations capturePrefix callerPrefix) := by
  constructor
  · intro scope mapping world heap store canonical id type value entry
    obtain ⟨entry⟩ := entry
    refine ⟨entry.authority, ?_⟩
    intro header member
    have index : ((id, type) :: scope).length + callerPrefix + header.slot =
        (scope.length + callerPrefix + header.slot) + 1 := by simp only [List.length_cons]; omega
    rw [index]
    exact entry.globals header member
  · intro scope mapping world heap store canonical id type value entry
    obtain ⟨entry⟩ := entry
    refine ⟨entry.authority, ?_⟩
    intro header member
    have index : ((id, type) :: scope).length + callerPrefix + header.slot =
        (scope.length + callerPrefix + header.slot) + 1 := by simp only [List.length_cons]; omega
    have selected := entry.globals header member
    rw [index] at selected
    exact selected

/-- Temporary actual binders transport only variable positions. They do not
modify the retained catalog, captured values or physical locations. -/
theorem Entry.reindex {scope : Scope} {canonical actual : Environment} {ξ : Renaming}
    (entry : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (agrees : EnvironmentsAgree ξ canonical actual) :
    ∀ header, header ∈ headers → actual[ξ (scope.length + callerPrefix + header.slot)]? = some
      (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) := by
  intro header member
  exact agrees (entry.globals header member)

private theorem insert_at_suffix (added suffix : Environment) (value : Value) :
    Environment.insertAt (added ++ suffix) added.length value = added ++ value :: suffix := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head tail ih => simpa [Environment.insertAt] using congrArg (List.cons head) ih

private theorem insert_administrative {administrative : Core.Context} {scope : Scope}
    {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type ambient.definitions) :
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      (type :: administrative) scope environment (Environment.insertAt canonical scope.length value) ambient.definitions := by
  induction related with
  | nil values => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed values)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih

/-- This receipt describes the completed parameter prefix and the next real
body environment. It contains a finite continuation agreement but no body
execution or body correspondence. -/
structure ParameterEntry (headers : Inventory prepared values ambient.definitions program)
    (locations : Locations) (capturePrefix : Nat)
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (header : Header prepared values ambient.definitions program)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative actualContext : Core.Context)
    (actual : Environment) (ξ : Renaming) (frameLocation : Location) (current : NativeFrame) (ghost : GhostFrame) where private mk ::
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate [] before header.function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap header.context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  actualTyped : RuntimeEnvironmentHasTypes world actualBody
    (CallableIndexedParameterTyped.prefixContext header.bindings actualContext) ambient.definitions
  catalog : Entry headers locations capturePrefix (capturePrefix + 1)
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) mapping world heap store canonical
  reference : canonical[header.bindings.length + 1 + header.globals]? =
    some (.cellRef prepared.layout.frame.type frameLocation)
  state : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame frameLocation current ghost store
  catalog_frame : catalog.authority.frameLocation = frameLocation
  catalog_current : catalog.authority.current = current
  catalog_ghost : catalog.authority.ghost = ghost
  agreement : ContinuationAgreement actual initialStore (header.parameterCode.rename ξ)
    actualBody store (header.body.rename embedding)

/-- Parameter allocation depends on the captured layout and independent
source locals, so callers can retain their represented closure's exact payload
without replacing it with a separately read catalogue closure. -/
theorem parameters_of_layout (authority : Authority headers locations capturePrefix mapping world heap store)
    {header : Header prepared values ambient.definitions program}
    {administrative : Core.Context} {canonical : Environment}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative [] [] canonical ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees heap header.function.context.locals [])
    (reference : canonical[header.globals]? = some (.cellRef prepared.layout.frame.type authority.frameLocation))
    (coherent : ∀ target, target ∈ headers → canonical[capturePrefix + target.slot]? = some
      (.cellRef (OptionalCell.cellType target.named.signature.functionType) (locations target)))
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    {actual actualContext ξ}
    (agrees : EnvironmentsAgree ξ (DataPatternValues.packValues payloads :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions) :
    Nonempty (ParameterEntry headers locations capturePrefix functions registry header arguments heap store mapping world
      administrative actualContext actual ξ authority.frameLocation authority.current authority.ghost) := by
  have tree := CallableIndexedParameterCertificates.of_accepted header.onError header.acceptedPrefix
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical
      (DataPatternValues.packValues payloads :: canonical) := by
    intro index value found; exact found
  have length : (header.bindings.map Prod.snd).length = payloads.length := by simpa using represented.length.2
  obtain ⟨environment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
    allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, _, lookups, spine, finalTyped, agreement⟩ :=
    CallableIndexedParameterTyped.prefix_typed tree header.definitions_eq header.registered represented environments heaps
      sourceLayout agrees actualTyped (allTypes := header.bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds header.inputs)
      (by simpa using reference) authority.frame.read authority.unmapped
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have bundleTyped := (CallableIndexedParameters.Arguments.pack_typed represented).weaken worlds
  have finalWithBundle := insert_administrative finalEnvironments bundleTyped
  have scopeLength : (header.bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length = header.bindings.length := by simp
  have exactEnvironment : Environment.insertAt finalCanonical header.bindings.length
      (DataPatternValues.packValues payloads) = finalLogical := by
    rw [canonicalEq, ← prefixLength, insert_at_suffix, logicalEq]
  rw [scopeLength, exactEnvironment, CallableIndexedParameters.scope_eq] at finalWithBundle
  rw [← header.parameters] at allocated
  have metadata := GenericLexicalContext.binders_metadata allocated
  let catalog : Entry headers locations capturePrefix (capturePrefix + 1)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld finalHeap finalStore finalLogical := by
    refine ⟨authority.extend maps worlds preservation metadata, ?_⟩
    intro target targetMember
    rw [logicalEq]
    simp only [List.length_map, List.length_reverse]
    have index : header.bindings.length + (capturePrefix + 1) + target.slot =
        added.length + (capturePrefix + target.slot + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using coherent target targetMember
  have finalReference : finalLogical[header.bindings.length + 1 + header.globals]? =
      some (.cellRef prepared.layout.frame.type authority.frameLocation) := by
    rw [logicalEq]
    have index : header.bindings.length + 1 + header.globals = added.length + (header.globals + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
  have current := CallableIndexedBodyFrames.body_current authority.unmapped authority.frame preservation
  have mono := FunctionCallBody.mono_binders header.extended
  exact ⟨⟨environment, finalHeap, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
    allocated, by simpa using finalWithBundle, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 locals allocated,
    maps, worlds, preservation, metadata, lookups, finalTyped, catalog, finalReference, current, (by rfl), (by rfl), (by
      change (authority.extend maps worlds preservation metadata).ghost = authority.ghost
      rfl), agreement⟩⟩

/-- The actual marked prefix constructs all source binders and preserves every
shared global reference. Its real suffix and packed-argument slot fix the body
catalog indices; no final environment typing or catalog entry is assumed. -/
theorem parameters (authority : Authority headers locations capturePrefix mapping world heap store)
    {header : Header prepared values ambient.definitions program} (_member : header ∈ headers)
    (capture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap store)
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    {actual actualContext ξ}
    (agrees : EnvironmentsAgree ξ (DataPatternValues.packValues payloads :: capture.canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions) :
    Nonempty (ParameterEntry headers locations capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual ξ authority.frameLocation authority.current authority.ghost) := by
  exact parameters_of_layout authority capture.environments capture.locals capture.reference capture.coherent
    represented heaps agrees actualTyped

/-- The named hook and the real marked parameter prefix together produce a
body entry for the whole catalog. The saved caller frame and write-result Unit
are the actual administrative prefix slots. No body execution is required. -/
theorem named_parameters (authority : Authority headers locations capturePrefix mapping world heap store)
    {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store) :
    ∃ origin index metadata,
      prepared.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      header.code = withFrame (.var (base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) header.parameterCode ∧
      ∃ capture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap store,
        Nonempty (ParameterEntry headers locations capturePrefix functions registry header arguments heap
          (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) mapping world
          capture.administrative
          (.unit :: prepared.layout.frame.type :: header.named.signature.parameterType :: capture.capturedContext)
          (.unit :: encode prepared.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured)
          (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift))
          authority.frameLocation (.state index) (.named origin)) := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared header.hook
  obtain ⟨capture⟩ := authority.captures header member
  have written : store.write? authority.frameLocation (encode prepared.layout.frame (.state index)) =
      some (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp authority.frame.read).1, rfl⟩
  let installed := authority.install (.stable history)
  let nextCapture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap
      (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) :=
    { capture with read := (Store.write?_preserves_other written capture.distinct).trans capture.read }
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift))
      (DataPatternValues.packValues payloads :: capture.canonical)
      (.unit :: encode prepared.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured) :=
    GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift capture.layout (DataPatternValues.packValues payloads))
      (encode prepared.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType ambient.definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (definitions := ambient.definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped capture.typed))
  have entry := parameters installed member nextCapture represented installedHeaps layout actualTyped
  exact ⟨origin, index, metadata, owned, history, emitted, capture, entry⟩

/-- Restore also recovers the complete caller entry, rather than just its
current frame token. The caller's own lexical lookup positions stay unchanged. -/
theorem Entry.restored {scope : Scope} {canonical : Environment}
    (entry : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    {next : NativeFrame} {functions : FunctionModel values.checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry}
    (registered : prepared.layout.frame.Registered ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after futureStore)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping
      (store.set entry.authority.frameLocation (encode prepared.layout.frame next)) futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after
      (futureStore.set entry.authority.frameLocation (encode prepared.layout.frame entry.authority.current)) ∧
    Nonempty (Entry headers locations capturePrefix callerPrefix scope futureMap futureWorld after
      (futureStore.set entry.authority.frameLocation (encode prepared.layout.frame entry.authority.current)) canonical) := by
  obtain ⟨finalHeaps, restored, _⟩ := CallableIndexedBodyFrames.restore registered entry.authority.unmapped entry.authority.typed
    entry.authority.frame heaps worlds frame
  exact ⟨finalHeaps, ⟨entry.extend maps worlds restored metadata⟩⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
