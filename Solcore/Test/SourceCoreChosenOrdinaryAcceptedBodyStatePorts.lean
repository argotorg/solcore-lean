import Solcore.Test.SourceCoreChosenOrdinaryAcceptedHeader
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedParameterReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationHeads

/-! The real empty parameter allocation retains its Source heap and lexical
environment. The same reached receipt supplies captures, native observations,
the principal packet, marked readiness and deep Source admission. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedBodyStatePorts
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering Core
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open Tests.SourceCoreChosenOrdinaryAcceptedFixture
open Tests.SourceCoreChosenOrdinaryAcceptedHeader

variable (fixture : AcceptedFixture) {header : ActualHeader fixture}
  (atHeader : HeaderAt fixture header)
  {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {initial : ProtectedStateTransition.Index}
  {argumentsPool : State headers keys initial} {arguments : List Dynamic.Value}
  (receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt
    (registry := registry) functions owner argumentsPool header arguments)

include atHeader in
/-- The genuine Header parameter equation fixes the exact empty binding list. -/
theorem bindings_empty : header.bindings = [] := by
  have same : header.bindings.map Prod.fst = [] := header.parameters.symm.trans atHeader.parameters
  exact List.map_eq_nil_iff.mp same

private theorem empty_allocation {before heap : Dynamic.Heap} {values : List Dynamic.Value}
    {environment : Dynamic.Environment}
    (allocated : Dynamic.BindersAllocate [] before [] values environment heap) :
    values = [] ∧ environment = [] ∧ heap = before := by
  cases allocated
  exact ⟨rfl, rfl, rfl⟩

include atHeader in
/-- Empty parameters admit only the original nil allocation constructor. -/
theorem empty_entry : arguments = [] ∧ receipt.body.environment = [] ∧ receipt.body.heap = initial.heap := by
  have allocation := receipt.body.allocation
  rw [atHeader.parameters] at allocation
  exact empty_allocation allocation

include atHeader in
/-- The Header and fixture scopes denote the same literal empty Source scope. -/
theorem scope_at_entry :
    header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) = initialScope fixture.packet := by
  exact congrArg (fun bindings => bindings.reverse.map (fun binding => (binding.1.id, binding.2))) atHeader.bindings

include atHeader in
theorem scope_empty : initialScope fixture.packet = [] := by
  rw [← scope_at_entry fixture atHeader, bindings_empty fixture atHeader]
  rfl

include atHeader in
/-- The actual parameter temporaries vanish only because their binding list is empty. -/
theorem actual_environment_typed : RuntimeEnvironmentHasTypes receipt.body.world receipt.body.actualBody
    receipt.actualContext fixture.packet.compiled.indexed.layouts.definitions := by
  simpa only [bindings_empty fixture atHeader, CallableIndexedParameterTyped.prefixContext, List.foldl_nil, SourceCoreCompatibleValues.Context.initial, CallableIndexedAmbient.ambientDefinitions]
    using receipt.body.actualTyped

/-- Store typing is an original field of the same receiving-model heap relation. -/
theorem runtime_store_typed : RuntimeStoreHasTypes receipt.body.world receipt.body.store
    fixture.packet.compiled.indexed.layouts.definitions := receipt.body.heaps.runtime_hasTypes

include atHeader in
theorem source_heap_typed : Dynamic.HeapWellTyped (runtimeContext fixture.packet) receipt.body.heap := by
  rw [(empty_entry fixture atHeader functions owner receipt).2.2, ← atHeader.functionContext]
  exact receipt.heapTyped

include atHeader in
theorem source_locals : Dynamic.EnvironmentAgrees receipt.body.heap (runtimeContext fixture.packet).locals [] := by
  simpa only [atHeader.context, (empty_entry fixture atHeader functions owner receipt).2.1] using receipt.body.locals

/-- Catalog, carried Source metadata, bundle and frame come from the same entry. -/
def formation_entry (prefixZero : owner.key.capturePrefix = 0) :
    CallableIndexedLambdaNestedFormationEntries.Entry
      (values := .initial fixture.packet.compiled.compatible.checked)
      (indexed := fixture.packet.compiled.indexed)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram) header headers owner.key.locations 0 1
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      receipt.body.mapping receipt.body.world receipt.body.heap receipt.body.store receipt.body.canonical where
  catalog := {
    authority := {
      frameLocation := receipt.body.catalog.authority.frameLocation
      unmapped := receipt.body.catalog.authority.unmapped
      typed := receipt.body.catalog.authority.typed
      current := receipt.body.catalog.authority.current
      ghost := receipt.body.catalog.authority.ghost
      frame := receipt.body.catalog.authority.frame
      records := receipt.body.catalog.authority.records
      snapshots := receipt.body.catalog.authority.snapshots
      distinct := receipt.body.catalog.authority.distinct
      captures := by
        intro target member
        obtain ⟨capture⟩ := receipt.body.catalog.authority.captures target member
        exact ⟨{ capture with
          coherent := by
            intro other retained
            simpa only [prefixZero] using capture.coherent other retained }⟩ }
    globals := by
      intro target member
      simpa only [prefixZero, Nat.zero_add] using receipt.body.catalog.globals target member }
  history := by
    simpa only [receipt.body.catalog_current, receipt.body.catalog_ghost, SourceCoreCompatibleValues.Context.initial] using receipt.allowed.2
  bundle := CallableIndexedLambdaNestedFormationEntries.bundle_of_environment receipt.body.environments
    (by rw [header.parameterType]; rfl)
  reference := by
    simpa only [List.length_map, List.length_reverse, receipt.body.catalog_frame] using receipt.body.reference

/-- Construct the finite creator capture without replaying the parameter prefix. -/
def captures_at_entry
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := fixture.packet.compiled.indexed.ancestry)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed) headers)
    (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = fixture.packet.compiled.indexed.base.globals.length) :
    CallableIndexedLambdaValues.Captures fixture.packet.compiled.indexed receipt.body.mapping receipt.body.world
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      receipt.body.environment receipt.body.actualBody :=
  RecursiveNamedLambdaFormationHeads.captures_for complete globals
    (formation_entry fixture functions owner receipt prefixZero)
    receipt.body.environments receipt.body.lookups receipt.body.actualTyped

theorem captures_prefix
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := fixture.packet.compiled.indexed.ancestry)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed) headers)
    (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = fixture.packet.compiled.indexed.base.globals.length) :
    (captures_at_entry fixture functions owner receipt complete prefixZero globals).administrative =
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) header := rfl

theorem captures_embedding
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := fixture.packet.compiled.indexed.ancestry)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed) headers)
    (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = fixture.packet.compiled.indexed.base.globals.length) :
    (captures_at_entry fixture functions owner receipt complete prefixZero globals).embedding = receipt.body.embedding := rfl

/-- Actual cached Header slots bound the capture; no global completeness inverse is used. -/
theorem captured_globals
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := fixture.packet.compiled.indexed.ancestry)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed) headers)
    (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = fixture.packet.compiled.indexed.base.globals.length) :
    CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      headers owner.key.locations 1
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (captures_at_entry fixture functions owner receipt complete prefixZero globals).canonical owner.key.frameLocation := by
  have observed := RecursiveNamedLambdaFormationHeads.capture_globals_for complete globals
    (RecursiveNamedLambdaFormationHeads.cached_capture_slots fixture.packet.compiled headers)
    (formation_entry fixture functions owner receipt prefixZero)
    receipt.body.environments receipt.body.lookups receipt.body.actualTyped
  simpa only [captures_at_entry, RecursiveNamedLambdaFormationHeads.captures_for,
    formation_entry, receipt.body.catalog_frame, receipt.physical] using observed

include atHeader in
/-- Deep Source typing and every installed row concern the unchanged reached pool. -/
theorem admission_at_entry (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = fixture.packet.compiled.indexed.base.globals.length) :
    Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
      (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner header))
      (runtimeContext fixture.packet) (receipt.nested prefixZero globals) :=
  ⟨source_heap_typed fixture atHeader functions owner receipt, receipt.rows⟩

/-- Actual stable owner history and the original current read supply marked readiness. -/
theorem ready_at_entry (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = fixture.packet.compiled.indexed.base.globals.length) :
    (CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) owner header
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)).Ready
      (receipt.nested prefixZero globals) receipt.frameLocation (.state receipt.index) := by
  apply CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner header
    (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions) receipt.stable_owner
  exact receipt.body.state.read

end Tests.SourceCoreChosenOrdinaryAcceptedBodyStatePorts
