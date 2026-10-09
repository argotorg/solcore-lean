import Solcore.Test.SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBootstrapGlobals
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitializationReceipts
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt

/-! The original public bootstrap supplies the concrete singleton catalog and
its positive initialized capture. One real named hook and parameter prefix
produce the same admission-bearing body receipt, without a Source body law. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicParameterEntry
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open CallableIndexedOwnedFunctionState RecursiveNamedCatalogInvocationBounds
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt

/-- The actual singleton header order and fixed physical initialization key. -/
def headers (fixture : AcceptedFixture) (header : ActualHeader fixture) := [header]

def key (fixture : AcceptedFixture) : CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram) :=
  ⟨fun header => RecursiveNamedCatalogInitialization.location fixture.packet.compiled.indexed.base.globals header.slot, 0, 0⟩

def keys (fixture : AcceptedFixture) := [key fixture]

def owner (fixture : AcceptedFixture) : CallableIndexedOwnedFunctionValues.OwnedKey (keys fixture) :=
  ⟨⟨0, by simp [keys]⟩⟩

theorem bindings_empty (fixture : AcceptedFixture) {header : ActualHeader fixture}
    (atHeader : HeaderAt fixture header) : header.bindings = [] := by
  have empty : header.bindings.map Prod.fst = [] := header.parameters.symm.trans atHeader.parameters
  exact List.map_eq_nil_iff.mp empty

theorem types_empty (fixture : AcceptedFixture) {header : ActualHeader fixture}
    (atHeader : HeaderAt fixture header) : header.types = [] := by
  have length := header.extended.length_eq
  rw [atHeader.parameters, List.length_nil] at length
  exact List.eq_nil_of_length_eq_zero length.symm

theorem locals_empty (fixture : AcceptedFixture) {header : ActualHeader fixture}
    (atHeader : HeaderAt fixture header) : header.function.context.locals = [] := by
  rw [atHeader.functionContext]
  rfl

theorem catalog_complete (fixture : AcceptedFixture) (prepared : PublicRecipeReceipt fixture)
    {header : ActualHeader fixture} (atHeader : HeaderAt fixture header) :
    RecursiveNamedCatalogNativeContexts.Complete
      (prepared := fixture.packet.compiled.indexed.ancestry) (values := .initial fixture.packet.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram) (headers fixture header) := by
  intro index signature found
  rw [CallableIndexedPreparedInventories.cached_globals, functions_singleton prepared] at found
  simp only [List.map_cons, List.map_nil] at found
  cases index with
  | zero =>
    have same : fixture.packet.named.signature = signature := Option.some.inj found
    exact ⟨header, List.mem_singleton_self header, atHeader.slot, atHeader.named ▸ same⟩
  | succ index => simp at found

theorem catalog_ledger (fixture : AcceptedFixture) {header : ActualHeader fixture}
    (atHeader : HeaderAt fixture header) :
    Ledger (headers fixture header) fixture.packet.compiled.indexed.secondPass.closures := by
  refine ⟨?_, ?_, ?_⟩
  · change [header.slot].Nodup
    simp
  · have programEq := (SourceCoreUnifiedPreparationCertificates.prepare_fields fixture.packet.compiledAccepted).1
    have ids := (Frontend.checkProgram_success_ids fixture.packet.checked).1
    have unique := (SignatureCatalogWellFormed.ofCheckProgram fixture.packet.checked).function_ids
    simp only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked]
    rw [programEq, ids]
    exact unique
  · intro selected member
    have same : selected = header := List.mem_singleton.mp member
    subst selected
    rw [atHeader.slot, atHeader.named, atHeader.code]
    exact fixture.packet.cached.trans (congrArg some fixture.tail.emitted)

/-- The actual returned Entry and prescribed capture share the completed
bootstrap store. Frame history and records are retained constructor facts. -/
structure InitialAt (fixture : AcceptedFixture) (header : ActualHeader fixture)
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) (world : StoreTyping) (store : Store) where
  catalog : Entry (prepared := fixture.packet.compiled.indexed.ancestry)
    (values := .initial fixture.packet.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)
    (headers fixture header) (key fixture).locations 0 0 [] [] world ⟨[]⟩ store
    (RecursiveNamedCatalogPreparedInitialization.environment fixture.packet.compiled)
  heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry functions
    [] world ⟨[]⟩ store
  frameLocation : catalog.authority.frameLocation = 0
  current : catalog.authority.current = .empty
  ghost : catalog.authority.ghost = .empty
  records : catalog.authority.records = []
  capture : Capture (prepared := fixture.packet.compiled.indexed.ancestry)
    (values := .initial fixture.packet.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)
    (headers fixture header) (key fixture).locations 0 0 header [] world ⟨[]⟩ store
  canonical : capture.canonical = RecursiveNamedCatalogPreparedInitialization.environment fixture.packet.compiled
  captured : capture.captured = List.replicate header.slot Value.unit ++
    RecursiveNamedCatalogPreparedInitialization.environment fixture.packet.compiled
  embedding : capture.embedding = RecursiveGlobalInitializationMeaning.shift header.slot

def InitialAt.state {fixture : AcceptedFixture} {header : ActualHeader fixture}
    {functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {store : Store}
    (initial : InitialAt fixture header functions registry world store) :
    State (headers fixture header) (keys fixture)
      ⟨[], [], world, ⟨[]⟩, store, RecursiveNamedCatalogPreparedInitialization.environment fixture.packet.compiled⟩ where
  rows i := by
    have same : i = (owner fixture).position := by
      apply Fin.ext
      have bound := i.isLt
      change i.val < 1 at bound
      change i.val = 0
      omega
    subst i
    exact ⟨initial.catalog.authority, initial.frameLocation⟩
  separated := by
    intro i j record member
    have same : i = (owner fixture).position := by
      apply Fin.ext
      have bound := i.isLt
      change i.val < 1 at bound
      change i.val = 0
      omega
    subst i
    change record ∈ initial.catalog.authority.records at member
    rw [initial.records] at member
    cases member

theorem InitialAt.stable {fixture : AcceptedFixture} {header : ActualHeader fixture}
    {functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {store : Store}
    (initial : InitialAt fixture header functions registry world store) :
    CallableIndexedOwnedIndirectExpressionHeads.StableRows initial.state := by
  intro i
  have same : i = (owner fixture).position := by
    apply Fin.ext
    have bound := i.isLt
    change i.val < 1 at bound
    change i.val = 0
    omega
  subst i
  change ∃ metadata, Carries fixture.packet.compiled.indexed.ancestry.graph.inputs
    fixture.packet.compiled.indexed.ancestry.graph.table initial.catalog.authority.current
      initial.catalog.authority.ghost metadata
  rw [initial.current, initial.ghost]
  exact ⟨none, .empty⟩

/-- One authentic preparation types the actual initialized store. The same
completed original machine supplies its exact store equality. -/
theorem initial_at_completed (fixture : AcceptedFixture) (prepared : PublicRecipeReceipt fixture)
    {fuel : Nat} (completed : CompletedBootstrap prepared fuel) {header : ActualHeader fixture}
    (bootstrap : BootstrapEvidence fixture header)
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) :
    ∃ world, Nonempty (InitialAt fixture header functions registry world completed.store) := by
  have sameStore := (completed_store completed).2
  rw [sameStore]
  have sizes : ∀ selected, selected ∈ headers fixture header →
      selected.globals = fixture.packet.compiled.indexed.base.globals.length := by
    intro selected member
    have same : selected = header := List.mem_singleton.mp member
    subst selected
    exact bootstrap.globals
  have locals : ∀ selected, selected ∈ headers fixture header → selected.function.context.locals = [] := by
    intro selected member
    have same : selected = header := List.mem_singleton.mp member
    subst selected
    exact locals_empty fixture bootstrap.toHeaderAt
  obtain ⟨world, catalog, heaps, constructed⟩ :=
    RecursiveNamedCatalogPreparedInitializationReceipts.entry_with_constructor
      (values := .initial fixture.packet.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram) fixture.packet.compiled (headers fixture header) (catalog_ledger fixture bootstrap.toHeaderAt)
      sizes locals prepared.accepted rfl functions registry
  obtain ⟨capture, captured⟩ := constructed.captures header (List.mem_singleton_self header)
  exact ⟨world, ⟨⟨catalog, heaps, constructed.frameLocation, constructed.current,
    constructed.ghost, constructed.records, capture, captured.canonical, captured.captured, captured.embedding⟩⟩⟩

private theorem readyAt_layout {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {first second : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    (same : first = second)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys) second frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

private theorem related_frame {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
    {initial : ProtectedStateTransition.Index} (saved : State headers keys initial)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {first second : Location} {next : Value} (same : first = second)
    (state : State headers keys ⟨scope, mapping, world, heap, store.set first next, canonical⟩)
    (related : Relates saved state) :
    Relates saved (Eq.mp (congrArg (fun location => State headers keys
      ⟨scope, mapping, world, heap, store.set location next, canonical⟩) same) state) := by
  cases same
  exact related

/-- The genuine original parameter prefix is retained beside its same body
input and reached pool. Both Source argument lists are actually empty. -/
def ParameterAgreement (fixture : AcceptedFixture) {header : ActualHeader fixture}
    {functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {store : Store}
    (initial : InitialAt fixture header functions registry world store)
    (receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
      functions (owner fixture) initial.state header []) : Prop :=
  ContinuationAgreement receipt.actual
    (store.set receipt.frameLocation (encode fixture.packet.compiled.indexed.ancestry.layout.frame (.state receipt.index)))
    (header.parameterCode.rename receipt.embedding) receipt.body.actualBody receipt.body.store
    (header.body.rename receipt.body.embedding)

/-- One real named hook installation and one original stateful parameter
producer yield the complete actual parameter Receipt and continuation prefix. -/
theorem parameters_at_initial (fixture : AcceptedFixture) {header : ActualHeader fixture}
    (bootstrap : BootstrapEvidence fixture header)
    {functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {store : Store}
    (initial : InitialAt fixture header functions registry world store) :
    ∃ receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
        functions (owner fixture) initial.state header [], ParameterAgreement fixture initial receipt := by
  let authority := initial.catalog.authority
  have frameZero : authority.frameLocation = 0 := initial.frameLocation
  have physical : authority.frameLocation = (owner fixture).key.frameLocation := frameZero
  obtain ⟨origin, index, metadata, selected, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history fixture.packet.compiled.indexed.ancestry header.hook
  let installed := CallableIndexedOwnedFunctionState.install initial.state (owner fixture).position (.stable history)
  let installedAuthority := authority.install (.stable history)
  have written : store.write? authority.frameLocation
      (encode fixture.packet.compiled.indexed.ancestry.layout.frame (.state index)) =
      some (store.set authority.frameLocation (encode fixture.packet.compiled.indexed.ancestry.layout.frame (.state index))) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp authority.frame.read).1, rfl⟩
  let nextCapture : Capture (prepared := fixture.packet.compiled.indexed.ancestry)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)
      (headers fixture header) (key fixture).locations 0 0 header [] world ⟨[]⟩
      (store.set authority.frameLocation (encode fixture.packet.compiled.indexed.ancestry.layout.frame (.state index))) :=
    { initial.capture with read := (Store.write?_preserves_other written
      (by simpa only [frameZero] using initial.capture.distinct)).trans initial.capture.read }
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) initial.capture.embedding.lift))
      (DataPatternValues.packValues ([] : List Value) :: initial.capture.canonical)
      (.unit :: encode fixture.packet.compiled.indexed.ancestry.layout.frame authority.current ::
        DataPatternValues.packValues ([] : List Value) :: initial.capture.captured) :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift initial.capture.layout .unit)
        (encode fixture.packet.compiled.indexed.ancestry.layout.frame authority.current)) .unit
  have represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      [] world header.bindings [] [] := by
    rw [bindings_empty fixture bootstrap.toHeaderAt]
    exact .nil
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues ([] : List Value))
      header.named.signature.parameterType (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed).definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed).definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped initial.capture.typed))
  let producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol (headers fixture header) (keys fixture))
      header.layouts fixture.packet.compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions) :=
    bootstrap.layouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer (headers fixture header) (keys fixture)
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation (.state index) :=
    readyAt_layout bootstrap.layouts _ (CallableIndexedOwnedAllocationProducer.readyAt_of_owner_eq
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      (owner fixture).position physical.symm history)
  let parameterInitial : State (headers fixture header) (keys fixture)
      ⟨[], [], world, ⟨[]⟩, store.set authority.frameLocation
        (encode fixture.packet.compiled.indexed.ancestry.layout.frame (.state index)), initial.capture.canonical⟩ :=
    Eq.mp (congrArg (fun location => State (headers fixture header) (keys fixture)
      ⟨[], [], world, ⟨[]⟩, store.set location
        (encode fixture.packet.compiled.indexed.ancestry.layout.frame (.state index)), initial.capture.canonical⟩)
      physical.symm) installed
  obtain ⟨entry, transition, agreement⟩ := CallableIndexedOwnedInvocationBounds.parameters_with_state installedAuthority
    nextCapture.environments nextCapture.locals (by
      change nextCapture.canonical[header.globals]? = some (.cellRef fixture.packet.compiled.indexed.ancestry.layout.frame.type authority.frameLocation)
      simpa only [frameZero] using nextCapture.reference)
    nextCapture.coherent represented
    (CallableIndexedBodyFrames.install header.registered initial.heaps authority.unmapped authority.typed
      authority.frame (.stable history)).1 layout actualTyped producer parameterInitial readyAt
  obtain ⟨reached, related⟩ := transition
  have installedRelated : Relates initial.state parameterInitial :=
    related_frame initial.state physical.symm installed
      (CallableIndexedOwnedFunctionState.install_related initial.state (owner fixture).position (.stable history))
  have heapTyped : Dynamic.HeapWellTyped header.function.context ⟨[]⟩ := by intro cell member; cases member
  have argumentsTyped : Dynamic.ValuesHaveTypes header.function.context ⟨[]⟩ [] header.types := by
    rw [types_empty fixture bootstrap.toHeaderAt]
    exact .nil
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
      functions (owner fixture) initial.state header [] := {
    origin := origin, index := index, metadata := metadata,
    administrative := initial.capture.administrative,
    actualContext := _, actual := _, embedding := _, frameLocation := authority.frameLocation,
    physical := physical, selected := selected, history := history, emitted := emitted,
    body := entry, reached := reached, related := installedRelated.trans related,
    stable := initial.stable, heapTyped := heapTyped, argumentsTyped := argumentsTyped }
  exact ⟨receipt, agreement⟩

/-- Public preparation and completion are supplied once by the retained
executable receipt; the genuine named parameter action is then constructed. -/
theorem parameter_entry (fixture : AcceptedFixture) (prepared : PublicRecipeReceipt fixture)
    {fuel : Nat} (completed : CompletedBootstrap prepared fuel) {header : ActualHeader fixture}
    (bootstrap : BootstrapEvidence fixture header)
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) :
    ∃ world, ∃ initial : InitialAt fixture header functions registry world completed.store,
      ∃ receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
        functions (owner fixture) initial.state header [], ParameterAgreement fixture initial receipt := by
  obtain ⟨world, ⟨initial⟩⟩ := initial_at_completed fixture prepared completed bootstrap functions registry
  obtain ⟨receipt, agreement⟩ := parameters_at_initial fixture bootstrap initial
  exact ⟨world, initial, receipt, agreement⟩

end Tests.SourceCoreChosenOrdinaryAcceptedPublicParameterEntry
