import Solcore.Test.SourceSemantics.CoreLowering.Chosen.OuterBodies
import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootSourceSignature
import Solcore.Test.SourceSemantics.CoreLowering.Chosen.Admission
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramOutcomeMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedProgramAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestorationAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedInvocationAdmission

/-!
# Chosen ordinary public tests

Public invocation, session entry and program outcomes of the accepted ordinary call.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicInvocation
/-! The actual public initial state supplies each original named invocation.
Its real parameter child is packaged directly as a receipt; the parameters
and caller restoration remain inside the original invocation producers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicInvocation
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState RecursiveNamedCatalog
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)

/-- Both invocation directions use this exact receiving model and catalog. -/
def functions (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :=
  CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
    (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.headers fixture caller)
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.keys fixture) registry faults inventory.contracts

variable {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {world : StoreTyping} {store : Store}
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
    (functions fixture root inventory registry faults) registry world store)

/-- Copy the prescribed positive capture verbatim, transporting only its
physical frame proofs to the same initial pool's selected row. -/
def capture_at_initial : Capture
    (prepared := fixture.packet.compiled.indexed.ancestry)
    (values := .initial fixture.packet.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.headers fixture caller)
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture).key.locations 0
    (initial.state.rows (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture).position).authority.frameLocation
    caller [] world ⟨[]⟩ store := by
  have frameZero : (initial.state.rows (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture).position).authority.frameLocation = 0 :=
    (initial.state.rows (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture).position).frame_eq
  exact {
    administrative := initial.capture.administrative
    canonical := initial.capture.canonical
    captured := initial.capture.captured
    capturedContext := initial.capture.capturedContext
    embedding := initial.capture.embedding
    environments := initial.capture.environments
    locals := initial.capture.locals
    layout := initial.capture.layout
    typed := initial.capture.typed
    reference := by simpa only [frameZero] using initial.capture.reference
    capturedReference := by simpa only [frameZero] using initial.capture.capturedReference
    coherent := initial.capture.coherent
    unmapped := initial.capture.unmapped
    distinct := by
      rw [frameZero]
      exact initial.capture.distinct
    read := initial.capture.read }

/-- The low invocation result retains the restored original caller pool and
all cumulative effects. It imposes no successful Source post admission. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  FunctionCalls.ResultRepresents
    (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry
      (functions fixture root inventory registry faults))
    finalMap finalWorld caller.function.resultType caller.output faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry
    (functions fixture root inventory registry faults) finalMap finalWorld after finalStore ∧
  LocationMap.Extends [] finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved [] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
  ProtectedStateTransition.Transition
    (protocol (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.headers fixture caller)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.keys fixture)) initial.state
    ⟨[], finalMap, finalWorld, after, finalStore,
      RecursiveNamedCatalogPreparedInitialization.environment fixture.packet.compiled⟩

variable (prepared : PublicRecipeReceipt fixture) (bootstrap : BootstrapEvidence fixture caller)
  (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
  (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
  (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata fixture.packet)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)
  (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt fixture)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)

include prepared bootstrap shape typing checked chosen outer extension in
/-- The callback consumes its actual produced entry, without running the
parameter action again or assuming a completed body meaning. -/
theorem source_continuation_at_initial (budget : Nat) :
    CallableIndexedOwnedInvocationBounds.SourceContinuation
      (functions := functions fixture root inventory registry faults) (registry := registry) (faults := faults)
      (header := caller) (arguments := [])
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) initial.state
      (CallableIndexedOwnedNamedCanonicalEntries.condition
        (functions fixture root inventory registry faults)
        (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) caller) budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation
    physical selected history emitted entry _agreement reached related _allowed child _strict
  have heapTyped : Dynamic.HeapWellTyped caller.function.context ⟨[]⟩ := by
    intro cell member
    cases member
  have argumentsTyped : Dynamic.ValuesHaveTypes caller.function.context ⟨[]⟩ [] caller.types := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.types_empty fixture bootstrap.toHeaderAt]
    exact .nil
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
      (functions fixture root inventory registry faults)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) initial.state caller [] := {
    origin := origin, index := index, metadata := metadata,
    administrative := administrative, actualContext := actualContext, actual := actual, embedding := ξ,
    frameLocation := frameLocation, physical := physical, selected := selected,
    history := history, emitted := emitted, body := entry, reached := reached, related := related,
    stable := initial.stable, heapTyped := heapTyped, argumentsTyped := argumentsTyped }
  intro outcome after trace
  exact SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence.source_body_at
    fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete fixture prepared bootstrap.toHeaderAt)
    rfl receipt extension child trace

include prepared bootstrap shape typing checked chosen outer extension in
/-- Native inversion supplies the genuine measured parameter child. The
receipt keeps that same entry and its independent reflected Source grade. -/
theorem native_continuation_at_initial (budget : Nat) :
    CallableIndexedOwnedInvocationBounds.NativeContinuation
      (functions := functions fixture root inventory registry faults) (registry := registry) (faults := faults)
      (header := caller) (arguments := [])
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) initial.state
      (CallableIndexedOwnedNamedCanonicalEntries.condition
        (functions fixture root inventory registry faults)
        (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) caller) budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
    physical selected history emitted _prefix _prefixWithin _restored entry reached related _allowed child _strict
  have heapTyped : Dynamic.HeapWellTyped caller.function.context ⟨[]⟩ := by
    intro cell member
    cases member
  have argumentsTyped : Dynamic.ValuesHaveTypes caller.function.context ⟨[]⟩ [] caller.types := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.types_empty fixture bootstrap.toHeaderAt]
    exact .nil
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
      (functions fixture root inventory registry faults)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) initial.state caller [] := {
    origin := origin, index := index, metadata := metadata,
    administrative := administrative, actualContext := actualContext, actual := actual, embedding := ξ,
    frameLocation := frameLocation, physical := physical, selected := selected,
    history := history, emitted := emitted, body := entry, reached := reached, related := related,
    stable := initial.stable, heapTyped := heapTyped, argumentsTyped := argumentsTyped }
  intro bodyValue bodyFinalStore completed
  exact SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence.native_body_at
    fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete fixture prepared bootstrap.toHeaderAt)
    rfl receipt extension child completed

include prepared bootstrap shape typing checked chosen outer extension in
/-- The original named producer performs its real parameter action and
physical caller restoration once. All returned effects concern this state. -/
theorem preserves_at_initial (budget : Nat) {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues ([] : List Value) :: initial.capture.captured) store
        (caller.code.rename initial.capture.embedding.lift) value finalStore ∧
      ResultAt fixture root inventory initial outcome after value finalStore finalMap finalWorld := by
  have represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry
        (functions fixture root inventory registry faults)) [] world caller.bindings [] [] := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.bindings_empty fixture bootstrap.toHeaderAt]
    exact .nil
  exact CallableIndexedOwnedInvocationBounds.invocation_preserves_bounded_at
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) bootstrap.layouts
    (CallableIndexedOwnedNamedCanonicalEntries.condition (functions fixture root inventory registry faults)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) caller)
    (CallableIndexedOwnedNamedCanonicalEntries.authorized (functions fixture root inventory registry faults)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) caller)
    budget initial.state (List.mem_singleton_self caller)
    (capture_at_initial fixture root inventory initial) represented initial.heaps
    (source_continuation_at_initial fixture root inventory initial prepared bootstrap shape typing checked chosen outer extension budget)
    trace within

include prepared bootstrap shape typing checked chosen outer extension in
/-- Reflect the actual original invocation, retaining an independent Source
cost and the same restored caller scope, records and cumulative effects. -/
theorem reflects_at_initial (budget : Nat) {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues ([] : List Value) :: initial.capture.captured)
      store (caller.code.rename initial.capture.embedding.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after ∧
      ResultAt fixture root inventory initial outcome after value finalStore finalMap finalWorld := by
  have represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry
        (functions fixture root inventory registry faults)) [] world caller.bindings [] [] := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.bindings_empty fixture bootstrap.toHeaderAt]
    exact .nil
  exact CallableIndexedOwnedInvocationBounds.invocation_reflects_bounded_at
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) bootstrap.layouts
    (CallableIndexedOwnedNamedCanonicalEntries.condition (functions fixture root inventory registry faults)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) caller)
    (CallableIndexedOwnedNamedCanonicalEntries.authorized (functions fixture root inventory registry faults)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) caller)
    budget initial.state (List.mem_singleton_self caller)
    (capture_at_initial fixture root inventory initial) represented initial.heaps
    (native_continuation_at_initial fixture root inventory initial prepared bootstrap shape typing checked chosen outer extension budget)
    completed within

/-- This pair is pointwise at one genuine completed-bootstrap initial state.
It retains the original invocation result, without a Session equivalence. -/
structure InvocationAtInitial : Prop where
  preserves : ∀ (budget : Nat) {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after → size ≤ budget →
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues ([] : List Value) :: initial.capture.captured) store
        (caller.code.rename initial.capture.embedding.lift) value finalStore ∧
      ResultAt fixture root inventory initial outcome after value finalStore finalMap finalWorld
  reflects : ∀ (budget : Nat) {size : Nat} {value : Value} {finalStore : Store},
    EvaluationSize size (DataPatternValues.packValues ([] : List Value) :: initial.capture.captured)
      store (caller.code.rename initial.capture.embedding.lift) value finalStore → size ≤ budget →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after ∧
      ResultAt fixture root inventory initial outcome after value finalStore finalMap finalWorld

include bootstrap shape typing checked chosen outer extension in
/-- Retain one authentic initial state at the actual completed public store.
Each meaning uses the original invocation's own parameter entry exactly once. -/
theorem at_completed {fuel : Nat} (completed : CompletedBootstrap prepared fuel) :
    ∃ world,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
        (functions fixture root inventory registry faults) registry world completed.store,
      InvocationAtInitial fixture root inventory first := by
  obtain ⟨nextWorld, ⟨first⟩⟩ := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.initial_at_completed
    fixture prepared completed bootstrap (functions fixture root inventory registry faults) registry
  refine ⟨nextWorld, first, ?_, ?_⟩
  · intro budget size outcome after trace within
    exact preserves_at_initial fixture root inventory first prepared bootstrap shape typing checked chosen outer extension budget trace within
  · intro budget size value finalStore nativeCompleted within
    exact reflects_at_initial fixture root inventory first prepared bootstrap shape typing checked chosen outer extension budget nativeCompleted within

end Tests.SourceCoreChosenOrdinaryAcceptedPublicInvocation
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicSessionEntry
/-! The actual public artifact and fresh bootstrap produce one ready Session.
Its retained completion supplies the same initial store for the proved body.
The native machine is executed only by the original public resume action. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicSessionEntry
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt

/-- The opaque public objects and erased receipts all belong to this one run. -/
structure PublicSessionFixture where
  fixture : AcceptedFixture
  prepared : PublicRecipeReceipt fixture
  artifact : SourceCoreIndexedSession.Artifact
  recipeAt : artifact.RecipeAt prepared.recipe
  checkpoint : SourceCoreIndexedSession.Bootstrap artifact
  initial : checkpoint.InitialAt prepared.recipe {}
  session : SourceCoreIndexedSession.Session artifact
  ready : checkpoint.resume bootstrapFuel = .ready session

/-- The original fixture and Recipe preparation run once. The receipt-bearing
public actions mint one artifact and checkpoint, then resume that checkpoint
once. Original validation errors and fuel exhaustion remain observable. -/
def accepted_public_session_fixture : IO (Except String PublicSessionFixture) := do
  match SourceCoreChosenOrdinaryAcceptedFixture.acceptedFixture with
  | .error error => pure (.error error)
  | .ok fixture =>
    match prepare_public fixture with
    | .error error => pure (.error error)
    | .ok prepared =>
      let opened ← prepared.recipe.openWithReceipt
      let started ← opened.val.bootstrapFreshWithReceipt prepared.recipe opened.property
      match ready : started.val.resume bootstrapFuel with
      | .ready session =>
        pure (.ok ⟨fixture, prepared, opened.val, opened.property,
          started.val, started.property, session, ready⟩)
      | .error error => pure (.error s!"public bootstrap validation: {reprStr error}")
      | .outOfFuel _ => pure (.error s!"public bootstrap exhausted fuel {bootstrapFuel}")

/-- Invert the retained ready equation only in a proof. The original completion
becomes the existing CompletedBootstrap; no store accessor or second run is used. -/
theorem completed_at_ready (actual : PublicSessionFixture) :
    ∃ completed : CompletedBootstrap actual.prepared bootstrapFuel,
      actual.session.BootstrappedFrom actual.checkpoint completed.store := by
  obtain ⟨value, store, done, _success, booted⟩ :=
    SourceCoreIndexedSession.Bootstrap.resume_ready_receipt actual.checkpoint bootstrapFuel actual.ready
  exact ⟨⟨value, store, actual.initial.native_done done⟩, booted⟩

def registry (actual : PublicSessionFixture) : SourceCoreRawMetadata.Registry :=
  actual.fixture.packet.compiled.compatible.checked.staticRegistry

theorem registry_at (actual : PublicSessionFixture) : actual.session.RegistryAt (registry actual) := by
  obtain ⟨completed, booted⟩ := completed_at_ready actual
  have atRegistry := booted.registry_at actual.initial
  simpa only [registry, compiled_eq actual.prepared] using atRegistry

theorem inert_prefix (actual : PublicSessionFixture) : actual.session.inertPrefix = {} := by
  obtain ⟨completed, booted⟩ := completed_at_ready actual
  exact booted.inert_prefix actual.initial

theorem function_count (actual : PublicSessionFixture) : actual.session.functionCount = 0 := by
  obtain ⟨completed, booted⟩ := completed_at_ready actual
  exact booted.function_count

variable (actual : PublicSessionFixture) {caller : ActualHeader actual.fixture}
  {compilation : Compilation actual.fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics actual.fixture.packet.compiled actual.fixture.packet.diagnostics)
    actual.fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root actual.fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory actual.fixture)
  {faults : FunctionCalls.FaultRep}

/-- The real ready Session and full body meaning share the original initialized
store and its unique native world. All Source/compiler facts remain genuine;
the Source body law and parameter receipt are conclusions. -/
theorem body_at_session
    (bootstrap : BootstrapEvidence actual.fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape actual.fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata actual.fixture)
    (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata actual.fixture.packet)
    (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt actual.fixture root)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt actual.fixture) :
    ∃ completed : CompletedBootstrap actual.prepared bootstrapFuel,
    ∃ world,
    ∃ initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
        (SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.functions actual.fixture root inventory
          (registry actual) faults) (registry actual) world completed.store,
    ∃ receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry actual)
        (SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.functions actual.fixture root inventory
          (registry actual) faults)
        (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner actual.fixture) initial.state caller [],
      actual.session.NativeAt world completed.store ∧ actual.session.RegistryAt (registry actual) ∧
      SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.BodyAtReceipt
        actual.fixture root inventory initial receipt := by
  obtain ⟨completed, booted⟩ := completed_at_ready actual
  have extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial actual.fixture.packet.compiled.compatible.checked).registry
      (registry actual) := SourceCoreRawMetadata.Extends.refl _
  obtain ⟨world, initial, receipt, body⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.at_completed actual.fixture root inventory
      actual.prepared completed bootstrap shape typing checked chosen outer extension
  have sameWorld : world = completed.store.map Core.Value.type := initial.heaps.runtime_hasTypes.world_eq
  have atNative : actual.session.NativeAt world completed.store := by
    rw [sameWorld]
    exact booted.native_at
  exact ⟨completed, world, initial, receipt, atNative, registry_at actual, body⟩

/-- The original named invocation and caller restoration use the same actual
ready Session's initialized store. The low invocation result keeps its full
returned pool and cumulative effects; stronger post admission is separate. -/
theorem invocation_at_session
    (bootstrap : BootstrapEvidence actual.fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape actual.fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata actual.fixture)
    (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata actual.fixture.packet)
    (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt actual.fixture root)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt actual.fixture) :
    ∃ completed : CompletedBootstrap actual.prepared bootstrapFuel,
    ∃ world,
    ∃ initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture root inventory
          (registry actual) faults) (registry actual) world completed.store,
      actual.session.NativeAt world completed.store ∧ actual.session.RegistryAt (registry actual) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocation.InvocationAtInitial
        actual.fixture root inventory initial := by
  obtain ⟨completed, booted⟩ := completed_at_ready actual
  have extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial actual.fixture.packet.compiled.compatible.checked).registry
      (registry actual) := SourceCoreRawMetadata.Extends.refl _
  obtain ⟨world, initial, invocation⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicInvocation.at_completed actual.fixture root inventory
      actual.prepared bootstrap shape typing checked chosen outer extension completed
  have sameWorld : world = completed.store.map Core.Value.type := initial.heaps.runtime_hasTypes.world_eq
  have atNative : actual.session.NativeAt world completed.store := by
    rw [sameWorld]
    exact booted.native_at
  exact ⟨completed, world, initial, atNative, registry_at actual, invocation⟩

/-- Exercises actual public readiness and its installed native globals. -/
def run : IO Unit := do
  match ← accepted_public_session_fixture with
  | .error error => throw (IO.userError error)
  | .ok actual =>
    unless actual.session.heapSize == 2 && actual.session.functionCount == 0 &&
        actual.session.installedGlobalsPresent do
      throw (IO.userError "the actual ready Session has invalid initial cells or globals")
    IO.println s!"accepted public Session: one artifact, one fresh checkpoint, one resume at fuel {bootstrapFuel}; ready with {actual.session.heapSize} native cells"

end Tests.SourceCoreChosenOrdinaryAcceptedPublicSessionEntry
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicResultObservation
/-! Observe the same finite named invocation's represented result. Successful
Word payloads have identical Source and native words; language failures retain
their genuine diagnostic relation. This proof does not execute or export a
value, and does not turn native completion into public export success. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicResultObservation
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence

/-- Observable payload or language failure, with the same original fault map. -/
inductive Observation (faults : FunctionCalls.FaultRep) :
    Dynamic.ExpressionOutcome → Core.Value → Prop where
  | word (value : Word) : Observation faults (.value (.word value))
      (.inRight .word (.word value))
  | fault {reason : Dynamic.SemanticFault} {token : Word}
      (related : faults reason token) : Observation faults (.fault reason)
      (.inLeft .word (.word token))

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  {compilation : CallableIndexedNamedGeneration.Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
    fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {world : StoreTyping} {store : Store}
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
    registry world store)

include inventory in
/-- The authenticated Header's output is the actual retained Word signature. -/
theorem output_word (bootstrap : BootstrapEvidence fixture caller) : caller.output = .word := by
  have same := caller.resultType
  rw [bootstrap.named] at same
  exact same.symm.trans inventory.resultType

/-- The receiving function model supplies the observation theorem. The
returned heap, pool and cumulative effects remain in the original ResultAt. -/
theorem observe (bootstrap : BootstrapEvidence fixture caller)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Core.Value} {finalStore : Store} {finalMap : GeneralHeap.LocationMap}
    {finalWorld : StoreTyping}
    (result : SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt fixture root inventory initial
      outcome after value finalStore finalMap finalWorld) : Observation faults outcome value := by
  have represented := result.1
  have output := output_word fixture inventory bootstrap
  rw [output] at represented
  cases represented with
  | value payload =>
    have observations : CompatibleEquality.FunctionObservations fixture.packet.compiled.compatible.checked.catalog
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
        (CallableIndexedLambdaValues.Identity fixture.packet.compiled.indexed) :=
      CallableIndexedOwnedChosenOrdinaryLambdaValues.observations root.root
      (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.headers fixture caller)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.keys fixture) registry faults inventory.contracts
    obtain ⟨word, sourceEq, nativeEq⟩ := CompatiblePlaceModifier.word_fields observations payload
    cases sourceEq
    cases nativeEq
    exact .word word
  | fault related => exact .fault related

theorem Observation.word_iff {faults : FunctionCalls.FaultRep}
    {outcome : Dynamic.ExpressionOutcome} {native : Core.Value} (observed : Observation faults outcome native)
    (word : Word) : outcome = .value (.word word) ↔ native = .inRight .word (.word word) := by
  cases observed with
  | word actual => simp only [Dynamic.ExpressionOutcome.value.injEq, Dynamic.Value.word.injEq,
      Core.Value.inRight.injEq, Core.Value.word.injEq, true_and]
  | fault related => simp

theorem Observation.fault_iff {faults : FunctionCalls.FaultRep}
    {outcome : Dynamic.ExpressionOutcome} {native : Core.Value} (observed : Observation faults outcome native) :
    (∃ reason, outcome = .fault reason) ↔ (∃ token, native = .inLeft .word (.word token)) := by
  cases observed with
  | word actual => simp
  | fault related => simp

end Tests.SourceCoreChosenOrdinaryAcceptedPublicResultObservation
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicRootStart
/-! Actual successful public startup selects the original singleton Header.
Its retained capture supplies the original call read. The named invocation
ports prove finite root completion, without replaying public startup or
bootstrap and without asserting successful public export. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicRootStart
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof RecursiveNamedCatalog
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt
open SourceCoreChosenOrdinaryAcceptedPublicSessionEntry

theorem recipe_at {artifact : Artifact} {recipe : Recipe} (atRecipe : artifact.RecipeAt recipe) :
    ArtifactRecipe artifact recipe := by
  cases artifact
  exact atRecipe

theorem session_state {artifact : Artifact} {session : Session artifact}
    {world : StoreTyping} {store : Store} (atNative : session.NativeAt world store) :
    SessionState session world store := by
  cases session
  exact atNative

private theorem recipe_unique {artifact : Artifact} {left right : Recipe}
    (a : ArtifactRecipe artifact left) (b : ArtifactRecipe artifact right) : left = right := by
  cases artifact
  exact a.symm.trans b

private theorem state_unique {artifact : Artifact} {session : Session artifact}
    {leftWorld rightWorld : StoreTyping} {leftStore rightStore : Store}
    (a : SessionState session leftWorld leftStore) (b : SessionState session rightWorld rightStore) :
    leftWorld = rightWorld ∧ leftStore = rightStore := by
  cases session
  exact ⟨a.1.symm.trans b.1, a.2.symm.trans b.2⟩

/-- Singleton completeness supplies the full selected Header. Empty native
inputs follow from the actual encoder typing, not a guessed source context. -/
theorem at_header_start {compiled : SourceCoreUnifiedCompilation.Compiled}
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : SourceSemantics.Program} (header : Header compiled.indexed.ancestry values ambient.definitions program)
    (complete : RecursiveNamedCatalogNativeContexts.Complete [header])
    (inputs : header.named.inputs = [])
    {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
    {artifact : Artifact} (session : Session artifact) (atRecipe : artifact.RecipeAt recipe)
    {world : StoreTyping} {store : Store} (atNative : session.NativeAt world store)
    {key : SourceCoreCalls.Key} {boundaryFuel : Nat} {checkpoint : Checkpoint artifact}
    (accepted : session.start key [] boundaryFuel = .ok checkpoint) :
    CheckpointInitial checkpoint
      (SourceCoreCalls.call header.named.signature header.slot (LanguageResult.success .unit) Word.zero)
      (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store := by
  have compiledEq := Recipe.prepare_compiled prepared
  subst compiled
  obtain ⟨actualRecipe, root, actualWorld, actualStore, native, encodedValues, started⟩ := actual_start session accepted
  have sameRecipe : actualRecipe = recipe := recipe_unique started.recipe_eq (recipe_at atRecipe)
  subst actualRecipe
  obtain ⟨rfl, rfl⟩ := state_unique started.state (session_state atNative)
  obtain ⟨selected, selection⟩ := started.selection prepared complete
  have sameHeader : selected = header := List.mem_singleton.mp selection.member
  subst selected
  have types : root.types = [] := by
    rw [selection.shape.1, inputs]
    rfl
  have typed := started.typed
  rw [types] at typed
  have empty : native = [] := by cases typed; rfl
  have body := selection.shape.2
  rw [types] at body
  change root.body = SourceCoreCalls.call header.named.signature header.slot (LanguageResult.success .unit) Word.zero at body
  simpa only [empty, List.reverse_nil, List.nil_append, body] using started.initial

variable (actual : PublicSessionFixture) {caller : ActualHeader actual.fixture}
  {compilation : Compilation actual.fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics actual.fixture.packet.compiled actual.fixture.packet.diagnostics) actual.fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root actual.fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory actual.fixture)
  {faults : FunctionCalls.FaultRep} {world : StoreTyping} {store : Store}
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture root inventory (registry actual) faults)
    (registry actual) world store)
  {boundaryFuel : Nat} (checkpoint : Checkpoint actual.artifact)

/-- This checkpoint and invocation use the same actual ready Session store.
The result remains the original low invocation result, including restoration. -/
structure RootAtInitial : Prop where
  accepted : actual.session.start actual.fixture.packet.named.signature.key [] boundaryFuel = .ok checkpoint
  machine : CheckpointInitial checkpoint
    (SourceCoreCalls.call caller.named.signature caller.slot (LanguageResult.success .unit) Word.zero)
    (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled) store
  invocation : SourceCoreChosenOrdinaryAcceptedPublicInvocation.InvocationAtInitial actual.fixture root inventory initial

/-- The actual catalog and prescribed capture fix the original initialized
cell and its full closure. No arbitrary value representation is inverted. -/
theorem read_at_initial :
    Evaluates (.unit :: RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled) store
      (OptionalCell.read caller.named.signature.functionType (.var (caller.slot + 1)) Word.zero)
      (.inRight .word (.closure caller.named.signature.parameterType
        (LanguageResult.resultType caller.named.signature.resultType)
        (caller.code.rename initial.capture.embedding.lift) initial.capture.captured)) store := by
  have reference : (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled)[caller.slot]? =
      some (.cellRef (OptionalCell.cellType caller.named.signature.functionType)
        ((SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.key actual.fixture).locations caller)) := by
    simpa only [List.length_nil, Nat.zero_add] using initial.catalog.globals caller (List.mem_singleton_self caller)
  exact OptionalCell.read_success Word.zero (.var reference) initial.capture.read

/-- The independent Source body yields a budget for this actual public root
call. The original invocation and caller restoration are executed once. -/
theorem preserves_root (atRoot : RootAtInitial (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      size caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt actual.fixture root inventory initial
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, body, result⟩ :=
    atRoot.invocation.preserves size trace (Nat.le_refl size)
  have argument : Evaluates (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled) store
      (LanguageResult.success .unit) (.inRight .word .unit) store := .inRight .unit
  have whole := SourceCoreCalls.call_success argument (read_at_initial actual root inventory initial) body
  obtain ⟨required, completes⟩ := evaluation_runStateful_complete_with_sufficient_fuel whole
  exact ⟨value, finalStore, finalMap, finalWorld, required,
    fun fuel enough => atRoot.machine.native_done_iff.mpr (completes fuel enough), result⟩

/-- Actual finite public native completion yields its strict invocation child.
Reflection retains an independent Source size and the same restored pool. -/
theorem reflects_root (atRoot : RootAtInitial (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {fuel : Nat} {value : Core.Value} {finalStore : Store}
    (done : checkpoint.NativeDone fuel value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt actual.fixture root inventory initial
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨size, evaluated⟩ := evaluation_has_size (runStateful_evaluation_sound (atRoot.machine.native_done_iff.mp done))
  have argument : Evaluates (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled) store
      (LanguageResult.success .unit) (.inRight .word .unit) store := .inRight .unit
  have reference : (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled)[caller.slot]? =
      some (.cellRef (OptionalCell.cellType caller.named.signature.functionType)
        ((SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.key actual.fixture).locations caller)) := by
    simpa only [List.length_nil, Nat.zero_add] using initial.catalog.globals caller (List.mem_singleton_self caller)
  obtain ⟨child, strict, body⟩ := RecursiveNamedCallBounds.call_body argument reference initial.capture.read evaluated
  exact atRoot.invocation.reflects size body (Nat.le_of_lt strict)

/-- Tie original successful startup to the genuine invocation at the same
ready Session. Selection uses both original preparation and first-find. -/
theorem at_session
    (bootstrap : BootstrapEvidence actual.fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape actual.fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata actual.fixture)
    (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata actual.fixture.packet)
    (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt actual.fixture root)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt actual.fixture)
    (accepted : actual.session.start actual.fixture.packet.named.signature.key [] boundaryFuel = .ok checkpoint) :
    ∃ completed : CompletedBootstrap actual.prepared bootstrapFuel,
    ∃ world,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture root inventory (registry actual) faults)
      (registry actual) world completed.store,
      actual.session.NativeAt world completed.store ∧
      RootAtInitial (boundaryFuel := boundaryFuel) actual root inventory first checkpoint := by
  obtain ⟨completed, nextWorld, first, atNative, _atRegistry, invocation⟩ :=
    invocation_at_session actual root inventory bootstrap shape typing checked chosen outer
  have complete := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete actual.fixture actual.prepared bootstrap.toHeaderAt
  have inputs : caller.named.inputs = [] := by
    rw [bootstrap.toHeaderAt.named]
    exact checked.named_inputs
  have machine := at_header_start (compiled := actual.fixture.packet.compiled)
    (values := .initial actual.fixture.packet.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions actual.fixture.packet.compiled.indexed)
    (program := Program.ofChecked actual.fixture.packet.compiled.sourceProgram) caller complete inputs actual.prepared.accepted actual.session actual.recipeAt atNative accepted
  refine ⟨completed, nextWorld, first, atNative, accepted, ?_, invocation⟩
  simpa only [RecursiveNamedPublicBootstrapGlobals.environment_eq] using machine

end Tests.SourceCoreChosenOrdinaryAcceptedPublicRootStart
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome
/-! The actual public run and the original admitted Source program share one
accepted fixture. Static checks retain equations on that fixture; startup and
resume run once. Completed results preserve the full invocation correspondence,
and a successful public export returns the same Word as the Source program. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedNamedGeneration
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt
open SourceCoreChosenOrdinaryAcceptedPublicSessionEntry

/-- Every receipt concerns the same unchanged original checked program. -/
structure StaticReceipt (fixture : AcceptedFixture) where
  selected : OriginalSelection fixture.packet
  checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata fixture.packet
  shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture
  typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture
  body : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph
  inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture
  catalog : SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission.OriginalCatalog fixture.packet

def staticReceipt (fixture : AcceptedFixture) : Except String (StaticReceipt fixture) := do
  let selected ← originalSelection fixture.packet
  let checked ← SourceCoreChosenOrdinaryAcceptedHeader.metadata fixture.packet
  let shape ← SourceCoreChosenOrdinaryAcceptedTyping.shape fixture
  let typing ← SourceCoreChosenOrdinaryAcceptedOuterTyping.metadata fixture
  let body ← SourceCoreChosenOrdinaryAcceptedBodyMetadata.receipt fixture.packet fixture.graph
  let inventory ← SourceCoreChosenOrdinaryAcceptedStaticInventory.inventory fixture
  let catalog ← SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission.originalCatalog fixture.packet
  pure ⟨selected, checked.down, shape, typing.down, body.down, inventory.down, catalog.down⟩

theorem StaticReceipt.stages {fixture : AcceptedFixture} (given : StaticReceipt fixture) :
    Staging.ProgramHasStages (Program.ofChecked fixture.packet.compiled.sourceProgram) :=
  SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission.program_has_stages
    given.catalog given.selected given.checked given.shape given.typing

private theorem recipe_unique {artifact : Artifact} {left right : Recipe}
    (a : ArtifactRecipe artifact left) (b : ArtifactRecipe artifact right) : left = right := by
  cases artifact
  exact a.symm.trans b

/-- The selected raw Source result determines the original checkpoint request. -/
theorem requested_result {compiled : SourceCoreUnifiedCompilation.Compiled}
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : SourceSemantics.Program} (header : Header compiled.indexed.ancestry values ambient.definitions program)
    (complete : RecursiveNamedCatalogNativeContexts.Complete [header])
    {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
    {artifact : Artifact} (session : Session artifact) (atRecipe : artifact.RecipeAt recipe)
    {key : SourceCoreCalls.Key} {boundaryFuel : Nat} {checkpoint : Checkpoint artifact}
    (accepted : session.start key [] boundaryFuel = .ok checkpoint) :
    checkpoint.ResultTypeAt header.function.resultType := by
  have compiledEq := Recipe.prepare_compiled prepared
  subst compiled
  obtain ⟨actualRecipe, root, world, store, native, encoded, started⟩ := actual_start session accepted
  have sameRecipe : actualRecipe = recipe :=
    recipe_unique started.recipe_eq (SourceCoreChosenOrdinaryAcceptedPublicRootStart.recipe_at atRecipe)
  subst actualRecipe
  obtain ⟨selected, selection⟩ := started.selection prepared complete
  have sameHeader : selected = header := List.mem_singleton.mp selection.member
  subst selected
  have result := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selection).2
  simpa only [result] using started.original.result_type_at atRecipe started.selected

variable (actual : PublicSessionFixture) {caller : ActualHeader actual.fixture}
  {compilation : Compilation actual.fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics actual.fixture.packet.compiled actual.fixture.packet.diagnostics) actual.fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root actual.fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory actual.fixture)
  {faults : FunctionCalls.FaultRep} {world : StoreTyping} {store : Store}
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture root inventory (registry actual) faults)
    (registry actual) world store)
  {boundaryFuel : Nat} (checkpoint : Checkpoint actual.artifact)

/-- Source admission, actual startup and the full invocation use one run. -/
structure ProgramAt : Prop where
  bootstrap : BootstrapEvidence actual.fixture caller
  stages : Staging.ProgramHasStages (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
  root : SourceCoreChosenOrdinaryAcceptedPublicRootStart.RootAtInitial
    (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint
  requested : checkpoint.ResultTypeAt .word

/-- The original static receipts construct admission and body meaning as
conclusions at the actual accepted checkpoint, without evaluating Source. -/
theorem at_started (given : StaticReceipt actual.fixture)
    (accepted : actual.session.start actual.fixture.packet.named.signature.key [] boundaryFuel = .ok checkpoint) :
    ∃ header : ActualHeader actual.fixture,
    ∃ selectedCompilation : Compilation actual.fixture.packet.compiled.indexed header.named
      (effectiveDiagnostics actual.fixture.packet.compiled actual.fixture.packet.diagnostics) actual.fixture.packet.namedCode,
    ∃ selectedRoot : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root actual.fixture header selectedCompilation,
    ∃ nextWorld nextStore,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture header
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture selectedRoot given.inventory (registry actual) faults)
      (registry actual) nextWorld nextStore,
      actual.session.NativeAt nextWorld nextStore ∧
      ProgramAt (boundaryFuel := boundaryFuel) actual selectedRoot given.inventory first checkpoint := by
  obtain ⟨header, bootstrap⟩ := header_exists_with_bootstrap actual.fixture given.selected given.checked
  obtain ⟨selectedCompilation, selectedRoot, ⟨chosen⟩⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.at_original_root
      actual.fixture bootstrap.toHeaderAt given.shape given.body given.inventory
  obtain ⟨outer⟩ := SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.of_body actual.fixture
  obtain ⟨completed, nextWorld, first, atNative, atRoot⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicRootStart.at_session actual selectedRoot given.inventory checkpoint
      bootstrap given.shape given.typing given.checked chosen outer accepted
  have requested := requested_result (compiled := actual.fixture.packet.compiled) header
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete actual.fixture actual.prepared bootstrap.toHeaderAt)
    actual.prepared.accepted actual.session actual.recipeAt accepted
  rw [given.typing.header_result bootstrap.toHeaderAt] at requested
  exact ⟨header, selectedCompilation, selectedRoot, nextWorld, completed.store, first, atNative,
    bootstrap, given.stages, atRoot, requested⟩

/-- Reflection retains the original admitted whole-program outcome, final
heap, restored owned pool and cumulative effects of this finite execution. -/
theorem native_completed_reflects_program
    (atProgram : ProgramAt (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {fuel : Nat} {value : Core.Value} {finalStore : Store}
    (done : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ outcome after ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt actual.fixture root inventory initial
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨size, outcome, after, finalMap, finalWorld, body, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicRootStart.reflects_root actual root inventory initial checkpoint atProgram.root done
  have heapTyped : Dynamic.HeapWellTyped caller.function.context ⟨[]⟩ := by intro cell member; cases member
  have argumentsTyped : Dynamic.ValuesHaveTypes caller.function.context ⟨[]⟩ [] caller.types := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.types_empty actual.fixture atProgram.bootstrap.toHeaderAt]
    exact .nil
  exact ⟨outcome, after, finalMap, finalWorld,
    RecursiveNamedProgramOutcomeMeaning.program_from_body caller atProgram.stages heapTyped argumentsTyped body.sound, result⟩

/-- Independent Source completion yields sufficient native fuel for the same
checkpoint. The Source and Core budgets need not be equal. -/
theorem program_has_sufficient_native_fuel
    (atProgram : ProgramAt (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt actual.fixture root inventory initial
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨size, body⟩ := RecursiveNamedCallBounds.BodyOutcome.has_size
    (RecursiveNamedProgramOutcomeMeaning.body_from_program caller executed)
  exact SourceCoreChosenOrdinaryAcceptedPublicRootStart.preserves_root
    actual root inventory initial checkpoint atProgram.root body

/-- Actual successful public export reflects to the identical Source Word.
Export acceptance is read from the retained completion, not inferred from
native typing. The same final store and full invocation relation remain. -/
theorem public_succeeded_reflects_program
    (atProgram : ProgramAt (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {fuel : Nat} {completion : Completion actual.artifact}
    (resumed : checkpoint.ResumeAt fuel boundaryFuel (.succeeded completion)) :
    ∃ word after finalStore finalMap finalWorld,
      completion.value = .word word ∧ completion.sourceType = .word ∧
      completion.session.NativeAt (finalStore.map Core.Value.type) finalStore ∧
      Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ (.value (.word word)) after ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt actual.fixture root inventory initial
        (.value (.word word)) after (.inRight .word (.word word)) finalStore finalMap finalWorld := by
  obtain ⟨generation, native, finalStore, done, succeeded⟩ := resumed.succeeded
  obtain ⟨outcome, after, finalMap, finalWorld, executed, result⟩ :=
    native_completed_reflects_program actual root inventory initial checkpoint atProgram done
  have observed := SourceCoreChosenOrdinaryAcceptedPublicResultObservation.observe
    actual.fixture root inventory initial atProgram.bootstrap result
  have decoded : ∃ payload, LanguageResult.decode? native = some (.succeeded payload) := by
    obtain ⟨_, payload, _, _, _, decoded, _⟩ := succeeded
    exact ⟨payload, decoded⟩
  obtain ⟨word, sourceEq, nativeEq⟩ :
      ∃ word, outcome = .value (.word word) ∧ native = .inRight .word (.word word) := by
    cases observed with
    | word word => exact ⟨word, rfl, rfl⟩
    | fault related => obtain ⟨payload, impossible⟩ := decoded; simp [LanguageResult.decode?] at impossible
  subst outcome
  subst native
  exact ⟨word, after, finalStore, finalMap, finalWorld,
    succeeded.word_value atProgram.requested, succeeded.source_type atProgram.requested,
    succeeded.native_at.2, executed, result⟩

/-- A Source Word result successfully crosses the same public boundary at
sufficient native fuel and a positive export budget. Resume is not replayed. -/
theorem program_word_preserved
    (atProgram : ProgramAt (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    (positive : 0 < boundaryFuel) {word : Word} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ (.value (.word word)) after) :
    ∃ finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → ∀ outcome, checkpoint.ResumeAt fuel boundaryFuel outcome →
        ∃ completion, outcome = .succeeded completion ∧ completion.value = .word word) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt actual.fixture root inventory initial
        (.value (.word word)) after (.inRight .word (.word word)) finalStore finalMap finalWorld := by
  obtain ⟨native, finalStore, finalMap, finalWorld, required, completes, result⟩ :=
    program_has_sufficient_native_fuel actual root inventory initial checkpoint atProgram executed
  have observed := SourceCoreChosenOrdinaryAcceptedPublicResultObservation.observe
    actual.fixture root inventory initial atProgram.bootstrap result
  have nativeEq := (observed.word_iff word).mp rfl
  subst native
  exact ⟨finalStore, finalMap, finalWorld, required,
    fun fuel enough outcome resumed => resumed.word_succeeded (completes fuel enough) atProgram.requested positive, result⟩

def nativeFuel : Nat := 10000
def boundaryBudget : Nat := 1024

/-- These values and erased receipts belong to one actual public action chain. -/
structure PublicRun where
  actual : PublicSessionFixture
  static : StaticReceipt actual.fixture
  checkpoint : Checkpoint actual.artifact
  accepted : actual.session.start actual.fixture.packet.named.signature.key [] boundaryBudget = .ok checkpoint
  outcome : Outcome actual.artifact
  resumed : checkpoint.ResumeAt nativeFuel boundaryBudget outcome

def accepted_public_program_run : IO (Except String PublicRun) := do
  match ← accepted_public_session_fixture with
  | .error error => pure (.error error)
  | .ok actual =>
    match staticReceipt actual.fixture with
    | .error error => pure (.error error)
    | .ok static =>
      match accepted : actual.session.start actual.fixture.packet.named.signature.key [] boundaryBudget with
      | .error error => pure (.error s!"public root validation: {reprStr error}")
      | .ok checkpoint =>
        let resumed ← checkpoint.resumeWithReceipt nativeFuel boundaryBudget
        pure (.ok ⟨actual, static, checkpoint, accepted, resumed.val, resumed.property⟩)

/-- A success retained by the actual public collector has genuine original
Source admission and the same full returned invocation correspondence. -/
theorem PublicRun.succeeded_reflects_program (given : PublicRun)
    (faults : FunctionCalls.FaultRep) {completion : Completion given.actual.artifact}
    (succeeded : given.outcome = .succeeded completion) :
    ∃ header : ActualHeader given.actual.fixture,
    ∃ selectedCompilation : Compilation given.actual.fixture.packet.compiled.indexed header.named
      (effectiveDiagnostics given.actual.fixture.packet.compiled given.actual.fixture.packet.diagnostics)
      given.actual.fixture.packet.namedCode,
    ∃ selectedRoot : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root
      given.actual.fixture header selectedCompilation,
    ∃ firstWorld firstStore,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt given.actual.fixture header
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions given.actual.fixture selectedRoot
        given.static.inventory (registry given.actual) faults)
      (registry given.actual) firstWorld firstStore,
      ProgramAt (boundaryFuel := boundaryBudget) given.actual selectedRoot given.static.inventory first given.checkpoint ∧
      given.actual.session.NativeAt firstWorld firstStore ∧
      ∃ word after finalStore finalMap finalWorld,
        completion.value = .word word ∧ completion.sourceType = .word ∧
        completion.session.NativeAt (finalStore.map Core.Value.type) finalStore ∧
        Dynamic.ProgramOutcome (Program.ofChecked given.actual.fixture.packet.compiled.sourceProgram)
          (RecursiveNamedProgramEntrySource.entry header []) ⟨[]⟩ (.value (.word word)) after ∧
        SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt given.actual.fixture selectedRoot
          given.static.inventory first (.value (.word word)) after (.inRight .word (.word word))
          finalStore finalMap finalWorld := by
  obtain ⟨header, selectedCompilation, selectedRoot, firstWorld, firstStore, first, native, atProgram⟩ :=
    at_started (faults := faults) given.actual given.checkpoint given.static given.accepted
  have resumed : given.checkpoint.ResumeAt nativeFuel boundaryBudget (.succeeded completion) := by
    rw [← succeeded]
    exact given.resumed
  exact ⟨header, selectedCompilation, selectedRoot, firstWorld, firstStore, first, atProgram, native,
    public_succeeded_reflects_program given.actual selectedRoot given.static.inventory first
      given.checkpoint atProgram resumed⟩

/-- Measure original catalog acceptance and the actual public Word result. -/
def run : IO Unit := do
  match ← accepted_public_program_run with
  | .error error => throw (IO.userError error)
  | .ok actual =>
    match actual.outcome with
    | .succeeded completion =>
      match completion.value with
      | .word word =>
        unless word == Word.ofNatModulo 7 && completion.sourceType == TypeSystem.Ty.word &&
            completion.session.functionCount == 0 && completion.session.installedGlobalsPresent do
          throw (IO.userError "the actual public program returned a different Word, type or session")
        IO.println s!"accepted original Source program: public Word 7 at native fuel {nativeFuel}; original catalog accepted, one root start and one resume"
      | _ => throw (IO.userError "the actual public program returned a non-Word value")
    | .failed reason _ => throw (IO.userError s!"public program language failure: {reason.toNat}")
    | .exportError error _ => throw (IO.userError s!"public program export validation: {reprStr error}")
    | .outOfFuel _ => throw (IO.userError s!"public program exhausted native fuel {nativeFuel}")

end Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission
/-! The original public program result retains its actual returned caller
state. Genuine Source execution supplies successful value and deep heap
typing; the saved stable rows follow the actual administrative effects.
Preservation and reflection consume the existing producers once. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt
open SourceCoreChosenOrdinaryAcceptedPublicSessionEntry

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {world : StoreTyping} {store : Store}
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
    registry world store)

local notation "bridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (headers := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.headers fixture caller)
  (keys := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.keys fixture)

/-- The final six semantic effects and this same returned pool remain joined.
Faults retain stable rows without claiming successful value or heap typing. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Core.Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  FunctionCalls.ResultRepresents
    (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults))
    finalMap finalWorld caller.function.resultType caller.output faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
    finalMap finalWorld after finalStore ∧
  LocationMap.Extends [] finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved [] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
  ∃ returned : State
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.headers fixture caller)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.keys fixture)
      ⟨[], finalMap, finalWorld, after, finalStore,
        RecursiveNamedCatalogPreparedInitialization.environment fixture.packet.compiled⟩,
    Relates initial.state returned ∧
    PostAdmission bridge caller.function.context caller.function.resultType outcome returned

/-- Forgetting admission reconstructs the original transition with the same
returned witness; no separate pool is introduced. -/
theorem ResultAt.forget {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Core.Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : ResultAt fixture root inventory initial outcome after value finalStore finalMap finalWorld) :
    SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt fixture root inventory initial
      outcome after value finalStore finalMap finalWorld := by
  obtain ⟨represented, heaps, maps, worlds, frame, metadata, returned, related, _post⟩ := result
  exact ⟨represented, heaps, maps, worlds, frame, metadata, returned, related⟩

/-- The actual admitted Source program and final administrative frame supply
successful typing and every stable row at the original transition witness. -/
theorem post_at_initial {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Core.Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (executed : Dynamic.ProgramOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ outcome after)
    (result : SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt fixture root inventory initial
      outcome after value finalStore finalMap finalWorld) :
    ResultAt fixture root inventory initial outcome after value finalStore finalMap finalWorld := by
  obtain ⟨represented, heaps, maps, worlds, frame, metadata, transition⟩ := result
  obtain ⟨returned, related, post⟩ :=
    CallableIndexedOwnedNamedProgramAdmission.after_program_transition bridge caller initial.state
      initial.stable executed frame transition
  exact ⟨represented, heaps, maps, worlds, frame, metadata, returned, related, post⟩

/-- A successful result is reusable Source admission at that same returned
state, with raw Source typing in the actual final heap. -/
theorem ResultAt.at_value {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    {value : Core.Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : ResultAt fixture root inventory initial (.value sourceValue) after value finalStore finalMap finalWorld) :
    ∃ returned : State
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.headers fixture caller)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.keys fixture)
      ⟨[], finalMap, finalWorld, after, finalStore,
        RecursiveNamedCatalogPreparedInitialization.environment fixture.packet.compiled⟩,
      Relates initial.state returned ∧
      Dynamic.ValueHasType caller.function.context after sourceValue caller.function.resultType ∧
      Admission bridge caller.function.context returned := by
  obtain ⟨_, _, _, _, _, _, returned, related, post⟩ := result
  have admitted := post.at_value
  exact ⟨returned, related, admitted.1, admitted.2⟩

end Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission

namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedNamedGeneration
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt
open SourceCoreChosenOrdinaryAcceptedPublicSessionEntry

variable (actual : PublicSessionFixture) {caller : ActualHeader actual.fixture}
  {compilation : Compilation actual.fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics actual.fixture.packet.compiled actual.fixture.packet.diagnostics) actual.fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root actual.fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory actual.fixture)
  {faults : FunctionCalls.FaultRep} {world : StoreTyping} {store : Store}
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture root inventory (registry actual) faults)
    (registry actual) world store)
  {boundaryFuel : Nat} (checkpoint : Checkpoint actual.artifact)
  (atProgram : SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.ProgramAt
    (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)

include atProgram

/-- Actual native completion reflects to the original program and its same
returned state, including successful Source admission and all stable rows. -/
theorem native_completed_reflects_program {fuel : Nat} {value : Core.Value} {finalStore : Store}
    (done : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ outcome after ∧
      ResultAt actual.fixture root inventory initial outcome after value finalStore finalMap finalWorld := by
  obtain ⟨outcome, after, finalMap, finalWorld, executed, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.native_completed_reflects_program
      actual root inventory initial checkpoint atProgram done
  exact ⟨outcome, after, finalMap, finalWorld, executed,
    post_at_initial actual.fixture root inventory initial executed result⟩

/-- Independent Source completion gives sufficient native fuel and admission
at the same restored caller; the two execution budgets stay independent. -/
theorem program_has_sufficient_native_fuel {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      ResultAt actual.fixture root inventory initial outcome after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, required, completes, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.program_has_sufficient_native_fuel
      actual root inventory initial checkpoint atProgram executed
  exact ⟨value, finalStore, finalMap, finalWorld, required, completes,
    post_at_initial actual.fixture root inventory initial executed result⟩

/-- A real successful public export retains its identical Source Word, final
native store and admitted original returned caller state. -/
theorem public_succeeded_reflects_program {fuel : Nat} {completion : Completion actual.artifact}
    (resumed : checkpoint.ResumeAt fuel boundaryFuel (.succeeded completion)) :
    ∃ word after finalStore finalMap finalWorld,
      completion.value = .word word ∧ completion.sourceType = .word ∧
      completion.session.NativeAt (finalStore.map Core.Value.type) finalStore ∧
      Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ (.value (.word word)) after ∧
      ResultAt actual.fixture root inventory initial (.value (.word word)) after
        (.inRight .word (.word word)) finalStore finalMap finalWorld := by
  obtain ⟨word, after, finalStore, finalMap, finalWorld, exported, typed, native, executed, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.public_succeeded_reflects_program
      actual root inventory initial checkpoint atProgram resumed
  exact ⟨word, after, finalStore, finalMap, finalWorld, exported, typed, native, executed,
    post_at_initial actual.fixture root inventory initial executed result⟩

/-- Source Word preservation keeps the same actual resume receipt, positive
export budget and final returned-state admission. -/
theorem program_word_preserved (positive : 0 < boundaryFuel) {word : Word} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ (.value (.word word)) after) :
    ∃ finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → ∀ outcome, checkpoint.ResumeAt fuel boundaryFuel outcome →
        ∃ completion, outcome = .succeeded completion ∧ completion.value = .word word) ∧
      ResultAt actual.fixture root inventory initial (.value (.word word)) after
        (.inRight .word (.word word)) finalStore finalMap finalWorld := by
  obtain ⟨finalStore, finalMap, finalWorld, required, exports, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.program_word_preserved
      actual root inventory initial checkpoint atProgram positive executed
  exact ⟨finalStore, finalMap, finalWorld, required, exports,
    post_at_initial actual.fixture root inventory initial executed result⟩

omit atProgram

/-- The actual accepted public collector retains the same original program
result and admitted returned state without replaying startup or resume. -/
theorem public_run_succeeded_reflects_program
    (given : SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.PublicRun)
    (faults : FunctionCalls.FaultRep) {completion : Completion given.actual.artifact}
    (succeeded : given.outcome = .succeeded completion) :
    ∃ header : ActualHeader given.actual.fixture,
    ∃ selectedCompilation : Compilation given.actual.fixture.packet.compiled.indexed header.named
      (effectiveDiagnostics given.actual.fixture.packet.compiled given.actual.fixture.packet.diagnostics)
      given.actual.fixture.packet.namedCode,
    ∃ selectedRoot : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root
      given.actual.fixture header selectedCompilation,
    ∃ firstWorld firstStore,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt given.actual.fixture header
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions given.actual.fixture selectedRoot
        given.static.inventory (registry given.actual) faults)
      (registry given.actual) firstWorld firstStore,
      SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.ProgramAt (boundaryFuel := SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.boundaryBudget) given.actual selectedRoot given.static.inventory first given.checkpoint ∧
      given.actual.session.NativeAt firstWorld firstStore ∧
      ∃ word after finalStore finalMap finalWorld,
        completion.value = .word word ∧ completion.sourceType = .word ∧
        completion.session.NativeAt (finalStore.map Core.Value.type) finalStore ∧
        Dynamic.ProgramOutcome (Program.ofChecked given.actual.fixture.packet.compiled.sourceProgram)
          (RecursiveNamedProgramEntrySource.entry header []) ⟨[]⟩ (.value (.word word)) after ∧
        ResultAt given.actual.fixture selectedRoot
          given.static.inventory first (.value (.word word)) after (.inRight .word (.word word))
          finalStore finalMap finalWorld := by
  obtain ⟨header, selectedCompilation, selectedRoot, firstWorld, firstStore, first, atProgram, native,
    word, after, finalStore, finalMap, finalWorld, exported, typed, finalNative, executed, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.PublicRun.succeeded_reflects_program
      given faults succeeded
  exact ⟨header, selectedCompilation, selectedRoot, firstWorld, firstStore, first, atProgram, native,
    word, after, finalStore, finalMap, finalWorld, exported, typed, finalNative, executed,
    post_at_initial given.actual.fixture selectedRoot given.static.inventory first executed result⟩

end Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission
/-! The actual accepted fixture's
strong body families retain lexical exit and admission inside the invocation's
original parameter/body witnesses. Caller admission concerns the same restored
pool; the body exit keeps its full original administrative context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState RecursiveNamedCatalog
open CallableIndexedOwnedSourceAdmission
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {world : StoreTyping} {store : Store}
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
    registry world store)

/-- Both contexts are the same actual closed declaration type world. Its
residual inference flag remains true, as in the original runtime context. -/
theorem caller_supports (atHeader : HeaderAt fixture caller) :
    Dynamic.TypeContextSupports caller.context caller.function.context := by
  rw [atHeader.context, atHeader.functionContext]
  exact Dynamic.TypeContextSupports.ofClosed rfl rfl rfl rfl rfl

/-- The six original returned effects accompany a single causal receipt.
Its extra retains the full body exit/post and the actual restored caller post. -/
def ResultAtWithExit (sourceParent : Nat) (nativeBudget : Option Nat)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  FunctionCalls.ResultRepresents
    (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults))
    finalMap finalWorld caller.function.resultType caller.output faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
    finalMap finalWorld after finalStore ∧
  LocationMap.Extends [] finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved [] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
  NamedInvocationFaultPostContracts.ReturnedAtWithExtra
    (functions := SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
    (registry := registry) (header := caller)
    NamedInvocationFaultPostContracts.Trivial
    (CallableIndexedOwnedPreparedNamedInvocationAdmission.restored_exit_admission_extra
      (functions := SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
      (registry := registry) (header := caller) initial.state caller.function.context
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture).position)
    sourceParent nativeBudget (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
    initial.state [] outcome after value finalMap finalWorld finalStore

/-- Select only the caller state retained in the causal body/restoration
receipt. The actual final store equation transports that same witness. -/
theorem ResultAtWithExit.to_post {sourceParent : Nat} {nativeBudget : Option Nat}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : ResultAtWithExit fixture root inventory initial sourceParent nativeBudget
      outcome after value finalStore finalMap finalWorld) :
    SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission.ResultAt fixture root inventory initial
      outcome after value finalStore finalMap finalWorld := by
  obtain ⟨represented, heaps, maps, worlds, frame, metadata, causal⟩ := result
  obtain ⟨origin, index, bodyMetadata, administrative, actualContext, actual, ξ,
    entry, parameterState, sourceSize, bodyStore, bodyState, selected, history, emitted,
    parameterRelated, bodyRelated, trace, smaller, evaluated, bodyPost, measured,
    related, sameStore, restoredCell, fromBody, fromCaller, sameRecords, extra, restoredFrame⟩ := causal
  have callerPost :
      PostAdmission CallableIndexedOwnedBodyRestorationAdmission.bridge
        caller.function.context caller.function.resultType outcome
        (CallableIndexedOwnedBodyRestoration.returned initial.state bodyState
          (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture).position) := extra.2
  subst finalStore
  exact ⟨represented, heaps, maps, worlds, frame, metadata,
    CallableIndexedOwnedBodyRestoration.returned initial.state bodyState
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture).position,
    fromCaller, callerPost⟩

/-- The legacy result is projected through the same bound returned state. -/
theorem ResultAtWithExit.forget {sourceParent : Nat} {nativeBudget : Option Nat}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : ResultAtWithExit fixture root inventory initial sourceParent nativeBudget
      outcome after value finalStore finalMap finalWorld) :
    SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt fixture root inventory initial
      outcome after value finalStore finalMap finalWorld :=
  SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission.ResultAt.forget
    fixture root inventory initial (ResultAtWithExit.to_post fixture root inventory initial result)

variable (prepared : PublicRecipeReceipt fixture) (bootstrap : BootstrapEvidence fixture caller)
  (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
  (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
  (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata fixture.packet)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)
  (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt fixture)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)

include prepared bootstrap shape typing checked chosen outer extension in
/-- Each genuine invocation parameter receipt receives the proved strong
body family once. The original invocation restores its saved caller once. -/
theorem preserves_at_initial (budget : Nat) {size : Nat}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues ([] : List Value) :: initial.capture.captured) store
        (caller.code.rename initial.capture.embedding.lift) value finalStore ∧
      ResultAtWithExit fixture root inventory initial size none
        outcome after value finalStore finalMap finalWorld := by
  have represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults))
      [] world caller.bindings [] [] := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.bindings_empty fixture bootstrap.toHeaderAt]
    exact .nil
  have heapTyped : Dynamic.HeapWellTyped caller.function.context ⟨[]⟩ := by
    intro cell member
    cases member
  have argumentsTyped : Dynamic.ValuesHaveTypes caller.function.context ⟨[]⟩ [] caller.types := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.types_empty fixture bootstrap.toHeaderAt]
    exact .nil
  have bodies : CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
      (functions := SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
      (owner := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
      (registry := registry) (faults := faults) caller budget :=
    SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts.source_bodies_for
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete fixture prepared bootstrap.toHeaderAt)
      rfl extension budget
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, _transition, causal⟩ :=
    CallableIndexedOwnedPreparedNamedInvocationAdmission.invocation_preserves_bounded_at_with_admission
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) bootstrap.layouts
      (CallableIndexedOwnedNamedCanonicalEntries.condition
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
        (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) caller)
      (CallableIndexedOwnedNamedCanonicalEntries.authorized
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
        (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) caller)
      budget initial.state (List.mem_singleton_self caller)
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.capture_at_initial fixture root inventory initial)
      represented initial.heaps caller.function.context initial.stable heapTyped argumentsTyped
      (caller_supports fixture bootstrap.toHeaderAt) bodies trace within
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, causal⟩

include prepared bootstrap shape typing checked chosen outer extension in
/-- Native reflection keeps its actual strict body child and an independent
Source grade, with the same original body exit and returned caller admission. -/
theorem reflects_at_initial (budget : Nat) {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues ([] : List Value) :: initial.capture.captured)
      store (caller.code.rename initial.capture.embedding.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after ∧
      ResultAtWithExit fixture root inventory initial sourceSize (some size)
        outcome after value finalStore finalMap finalWorld := by
  have represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults))
      [] world caller.bindings [] [] := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.bindings_empty fixture bootstrap.toHeaderAt]
    exact .nil
  have heapTyped : Dynamic.HeapWellTyped caller.function.context ⟨[]⟩ := by
    intro cell member
    cases member
  have argumentsTyped : Dynamic.ValuesHaveTypes caller.function.context ⟨[]⟩ [] caller.types := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.types_empty fixture bootstrap.toHeaderAt]
    exact .nil
  have bodies : CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
      (functions := SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
      (owner := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
      (registry := registry) (faults := faults) caller budget :=
    SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts.native_bodies_for
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete fixture prepared bootstrap.toHeaderAt)
      rfl extension budget
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
    frame, metadata, _transition, causal⟩ :=
    CallableIndexedOwnedPreparedNamedInvocationAdmission.invocation_reflects_bounded_at_with_admission
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) bootstrap.layouts
      (CallableIndexedOwnedNamedCanonicalEntries.condition
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
        (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) caller)
      (CallableIndexedOwnedNamedCanonicalEntries.authorized
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
        (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) caller)
      budget initial.state (List.mem_singleton_self caller)
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.capture_at_initial fixture root inventory initial)
      represented initial.heaps caller.function.context initial.stable heapTyped argumentsTyped
      (caller_supports fixture bootstrap.toHeaderAt) bodies completed within
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
    frame, metadata, causal⟩

/-- Both directions concern this one actual initial state and the original
parameter/body/restoration witnesses retained by each invocation. -/
structure InvocationAtInitialWithExit : Prop where
  preserves : ∀ (budget : Nat) {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after → size ≤ budget →
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues ([] : List Value) :: initial.capture.captured) store
        (caller.code.rename initial.capture.embedding.lift) value finalStore ∧
      ResultAtWithExit fixture root inventory initial size none
        outcome after value finalStore finalMap finalWorld
  reflects : ∀ (budget : Nat) {size : Nat} {value : Value} {finalStore : Store},
    EvaluationSize size (DataPatternValues.packValues ([] : List Value) :: initial.capture.captured)
      store (caller.code.rename initial.capture.embedding.lift) value finalStore → size ≤ budget →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after ∧
      ResultAtWithExit fixture root inventory initial sourceSize (some size)
        outcome after value finalStore finalMap finalWorld

/-- The low pair is a projection at the same input and returned witnesses. -/
theorem InvocationAtInitialWithExit.forget
    (meaning : InvocationAtInitialWithExit fixture root inventory initial) :
    SourceCoreChosenOrdinaryAcceptedPublicInvocation.InvocationAtInitial fixture root inventory initial := by
  constructor
  · intro budget size outcome after trace within
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result⟩ := meaning.preserves budget trace within
    exact ⟨value, finalStore, finalMap, finalWorld, evaluated,
      ResultAtWithExit.forget fixture root inventory initial result⟩
  · intro budget size value finalStore completed within
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ := meaning.reflects budget completed within
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace,
      ResultAtWithExit.forget fixture root inventory initial result⟩

include prepared bootstrap shape typing checked chosen outer extension in
/-- Static accepted body families construct both strong directions at the
supplied authentic initial state; no public action is replayed. -/
theorem at_initial : InvocationAtInitialWithExit fixture root inventory initial := by
  constructor
  · intro budget size outcome after trace within
    exact preserves_at_initial fixture root inventory initial prepared bootstrap shape typing checked chosen outer extension budget trace within
  · intro budget size value finalStore completed within
    exact reflects_at_initial fixture root inventory initial prepared bootstrap shape typing checked chosen outer extension budget completed within

include bootstrap shape typing checked chosen outer extension in
/-- One original initial-state factory consumes the same completed-bootstrap
proof. All body, parameter and restoration work remains in its invocation. -/
theorem at_completed {fuel : Nat} (completed : CompletedBootstrap prepared fuel) :
    ∃ nextWorld,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
      registry nextWorld completed.store,
      InvocationAtInitialWithExit fixture root inventory first := by
  obtain ⟨nextWorld, ⟨first⟩⟩ := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.initial_at_completed
    fixture prepared completed bootstrap
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults) registry
  exact ⟨nextWorld, first,
    at_initial fixture root inventory first prepared bootstrap shape typing checked chosen outer extension⟩

end Tests.SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission
/-! The actual ready Session supplies one strong initial invocation pair.
The public root call keeps that pair's causal body exit and caller admission,
with independent Source and native child grades. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof RecursiveNamedCatalog
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt
open SourceCoreChosenOrdinaryAcceptedPublicSessionEntry

variable (actual : PublicSessionFixture) {caller : ActualHeader actual.fixture}
  {compilation : Compilation actual.fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics actual.fixture.packet.compiled actual.fixture.packet.diagnostics) actual.fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root actual.fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory actual.fixture)
  {faults : FunctionCalls.FaultRep} {world : StoreTyping} {store : Store}
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture root inventory (registry actual) faults)
    (registry actual) world store)
  {boundaryFuel : Nat} (checkpoint : Checkpoint actual.artifact)

/-- The actual startup, native machine and strong invocation share one initial
store and capture. The legacy root is only a projection of this same pair. -/
structure RootAtInitialWithExit : Prop where
  accepted : actual.session.start actual.fixture.packet.named.signature.key [] boundaryFuel = .ok checkpoint
  machine : CheckpointInitial checkpoint
    (SourceCoreCalls.call caller.named.signature caller.slot (LanguageResult.success .unit) Word.zero)
    (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled) store
  invocation : SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.InvocationAtInitialWithExit
    actual.fixture root inventory initial

theorem RootAtInitialWithExit.forget
    (meaning : RootAtInitialWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint) :
    SourceCoreChosenOrdinaryAcceptedPublicRootStart.RootAtInitial
      (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint := by
  exact ⟨meaning.accepted, meaning.machine,
    SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.InvocationAtInitialWithExit.forget
      actual.fixture root inventory initial meaning.invocation⟩

/-- Source completion invokes the strong body pair once, then closes the
original public call. The resulting native fuel is independent of Source size. -/
theorem preserves_root
    (atRoot : RootAtInitialWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      size caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit
        actual.fixture root inventory initial size none
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, body, result⟩ :=
    atRoot.invocation.preserves size trace (Nat.le_refl size)
  have argument : Evaluates (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled) store
      (LanguageResult.success .unit) (.inRight .word .unit) store := .inRight .unit
  have whole := SourceCoreCalls.call_success argument
    (SourceCoreChosenOrdinaryAcceptedPublicRootStart.read_at_initial actual root inventory initial) body
  obtain ⟨required, completes⟩ := evaluation_runStateful_complete_with_sufficient_fuel whole
  exact ⟨value, finalStore, finalMap, finalWorld, required,
    fun fuel enough => atRoot.machine.native_done_iff.mpr (completes fuel enough), result⟩

/-- The real completed root exposes its strict native invocation child. That
child and its independent Source grade remain explicit in the causal receipt. -/
theorem reflects_root
    (atRoot : RootAtInitialWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {fuel : Nat} {value : Core.Value} {finalStore : Store}
    (done : checkpoint.NativeDone fuel value finalStore) :
    ∃ sourceSize nativeChildSize outcome after finalMap finalWorld,
      EvaluationSize nativeChildSize (DataPatternValues.packValues ([] : List Core.Value) :: initial.capture.captured)
        store (caller.code.rename initial.capture.embedding.lift) value finalStore ∧
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit
        actual.fixture root inventory initial sourceSize (some nativeChildSize)
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨size, evaluated⟩ :=
    evaluation_has_size (runStateful_evaluation_sound (atRoot.machine.native_done_iff.mp done))
  have argument : Evaluates (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled) store
      (LanguageResult.success .unit) (.inRight .word .unit) store := .inRight .unit
  have reference : (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled)[caller.slot]? =
      some (.cellRef (OptionalCell.cellType caller.named.signature.functionType)
        ((SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.key actual.fixture).locations caller)) := by
    simpa only [List.length_nil, Nat.zero_add] using initial.catalog.globals caller (List.mem_singleton_self caller)
  obtain ⟨child, strict, body⟩ :=
    RecursiveNamedCallBounds.call_body argument reference initial.capture.read evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    atRoot.invocation.reflects size body (Nat.le_of_lt strict)
  exact ⟨sourceSize, child, outcome, after, finalMap, finalWorld, body, trace, result⟩

/-- One proof inversion of the actual ready bootstrap feeds one original
initial-state factory. The strong pair belongs to that exact ready Session. -/
theorem invocation_at_session
    (bootstrap : BootstrapEvidence actual.fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape actual.fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata actual.fixture)
    (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata actual.fixture.packet)
    (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt actual.fixture root)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt actual.fixture) :
    ∃ completed : CompletedBootstrap actual.prepared bootstrapFuel,
    ∃ nextWorld,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture root inventory (registry actual) faults)
      (registry actual) nextWorld completed.store,
      actual.session.NativeAt nextWorld completed.store ∧ actual.session.RegistryAt (registry actual) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.InvocationAtInitialWithExit
        actual.fixture root inventory first := by
  obtain ⟨completed, booted⟩ := completed_at_ready actual
  have extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial actual.fixture.packet.compiled.compatible.checked).registry
      (registry actual) := SourceCoreRawMetadata.Extends.refl _
  obtain ⟨nextWorld, first, invocation⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.at_completed actual.fixture root inventory
      actual.prepared bootstrap shape typing checked chosen outer extension completed
  have sameWorld : nextWorld = completed.store.map Core.Value.type := first.heaps.runtime_hasTypes.world_eq
  have atNative : actual.session.NativeAt nextWorld completed.store := by
    rw [sameWorld]
    exact booted.native_at
  have atRegistry : actual.session.RegistryAt (registry actual) := by
    have observed := booted.registry_at actual.initial
    simpa only [registry, compiled_eq actual.prepared] using observed
  exact ⟨completed, nextWorld, first, atNative, atRegistry, invocation⟩
/-- The actual accepted startup and one strong ready-state factory construct
the original root machine together, without replaying startup or invocation. -/
theorem at_session
    (bootstrap : BootstrapEvidence actual.fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape actual.fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata actual.fixture)
    (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata actual.fixture.packet)
    (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt actual.fixture root)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt actual.fixture)
    (accepted : actual.session.start actual.fixture.packet.named.signature.key [] boundaryFuel = .ok checkpoint) :
    ∃ completed : CompletedBootstrap actual.prepared bootstrapFuel,
    ∃ nextWorld,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture root inventory (registry actual) faults)
      (registry actual) nextWorld completed.store,
      actual.session.NativeAt nextWorld completed.store ∧
      RootAtInitialWithExit (boundaryFuel := boundaryFuel) actual root inventory first checkpoint := by
  obtain ⟨completed, nextWorld, first, atNative, _atRegistry, invocation⟩ :=
    invocation_at_session actual root inventory bootstrap shape typing checked chosen outer
  have complete := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete
    actual.fixture actual.prepared bootstrap.toHeaderAt
  have inputs : caller.named.inputs = [] := by
    rw [bootstrap.toHeaderAt.named]
    exact checked.named_inputs
  have machine := SourceCoreChosenOrdinaryAcceptedPublicRootStart.at_header_start
    (compiled := actual.fixture.packet.compiled)
    (values := .initial actual.fixture.packet.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions actual.fixture.packet.compiled.indexed)
    (program := Program.ofChecked actual.fixture.packet.compiled.sourceProgram) caller complete inputs
    actual.prepared.accepted actual.session actual.recipeAt atNative accepted
  refine ⟨completed, nextWorld, first, atNative, accepted, ?_, invocation⟩
  simpa only [RecursiveNamedPublicBootstrapGlobals.environment_eq] using machine

end Tests.SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicProgramOutcomeWithExit
/-! The same accepted public run retains genuine body exit and caller
admission inside its original root invocation. The existing static collector
and public action receipts remain inputs; this companion performs no IO. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramOutcomeWithExit
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableIndexedNamedGeneration
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt
open SourceCoreChosenOrdinaryAcceptedPublicSessionEntry

variable (actual : PublicSessionFixture) {caller : ActualHeader actual.fixture}
  {compilation : Compilation actual.fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics actual.fixture.packet.compiled actual.fixture.packet.diagnostics) actual.fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root actual.fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory actual.fixture)
  {faults : FunctionCalls.FaultRep} {world : StoreTyping} {store : Store}
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture root inventory (registry actual) faults)
    (registry actual) world store)
  {boundaryFuel : Nat} (checkpoint : Checkpoint actual.artifact)

/-- The authentic static admission, requested result and strong root pair
belong to this same checkpoint and initial caller state. -/
structure ProgramAtWithExit : Prop where
  bootstrap : BootstrapEvidence actual.fixture caller
  stages : Staging.ProgramHasStages (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
  root : SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission.RootAtInitialWithExit
    (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint
  requested : checkpoint.ResultTypeAt .word

/-- The original program contract is a pure projection of the same root. -/
theorem ProgramAtWithExit.forget
    (meaning : ProgramAtWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint) :
    SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.ProgramAt
      (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint := by
  exact ⟨meaning.bootstrap, meaning.stages,
    SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission.RootAtInitialWithExit.forget
      actual root inventory initial checkpoint meaning.root,
    meaning.requested⟩

/-- The existing collector supplies one authentic Header and compiler root.
The strong ready-state factory is used once at the actual startup receipt. -/
theorem at_started
    (given : SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.StaticReceipt actual.fixture)
    (accepted : actual.session.start actual.fixture.packet.named.signature.key [] boundaryFuel = .ok checkpoint) :
    ∃ header : ActualHeader actual.fixture,
    ∃ selectedCompilation : Compilation actual.fixture.packet.compiled.indexed header.named
      (effectiveDiagnostics actual.fixture.packet.compiled actual.fixture.packet.diagnostics) actual.fixture.packet.namedCode,
    ∃ selectedRoot : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root actual.fixture header selectedCompilation,
    ∃ nextWorld nextStore,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture header
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture selectedRoot given.inventory (registry actual) faults)
      (registry actual) nextWorld nextStore,
      actual.session.NativeAt nextWorld nextStore ∧
      ProgramAtWithExit (boundaryFuel := boundaryFuel) actual selectedRoot given.inventory first checkpoint := by
  obtain ⟨header, bootstrap⟩ := header_exists_with_bootstrap actual.fixture given.selected given.checked
  obtain ⟨selectedCompilation, selectedRoot, ⟨chosen⟩⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.at_original_root
      actual.fixture bootstrap.toHeaderAt given.shape given.body given.inventory
  obtain ⟨outer⟩ := SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.of_body actual.fixture
  obtain ⟨completed, nextWorld, first, atNative, atRoot⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission.at_session
      actual selectedRoot given.inventory checkpoint bootstrap given.shape given.typing given.checked chosen outer accepted
  have requested := SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.requested_result
    (compiled := actual.fixture.packet.compiled) header
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete actual.fixture actual.prepared bootstrap.toHeaderAt)
    actual.prepared.accepted actual.session actual.recipeAt accepted
  rw [given.typing.header_result bootstrap.toHeaderAt] at requested
  exact ⟨header, selectedCompilation, selectedRoot, nextWorld, completed.store, first, atNative,
    bootstrap, given.stages, atRoot, requested⟩

/-- Native completion retains its actual invocation child grade and the
independent Source grade while admitting the same whole-program outcome. -/
theorem native_completed_reflects_program_with_exit
    (atProgram : ProgramAtWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {fuel : Nat} {value : Core.Value} {finalStore : Store}
    (done : checkpoint.NativeDone fuel value finalStore) :
    ∃ sourceSize nativeChildSize outcome after finalMap finalWorld,
      EvaluationSize nativeChildSize (DataPatternValues.packValues ([] : List Core.Value) :: initial.capture.captured)
        store (caller.code.rename initial.capture.embedding.lift) value finalStore ∧
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after ∧
      Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ outcome after ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit
        actual.fixture root inventory initial sourceSize (some nativeChildSize)
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, nativeChildSize, outcome, after, finalMap, finalWorld, child, body, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission.reflects_root
      actual root inventory initial checkpoint atProgram.root done
  have heapTyped : Dynamic.HeapWellTyped caller.function.context ⟨[]⟩ := by
    intro cell member
    cases member
  have argumentsTyped : Dynamic.ValuesHaveTypes caller.function.context ⟨[]⟩ [] caller.types := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.types_empty actual.fixture atProgram.bootstrap.toHeaderAt]
    exact .nil
  exact ⟨sourceSize, nativeChildSize, outcome, after, finalMap, finalWorld, child, body,
    RecursiveNamedProgramOutcomeMeaning.program_from_body caller atProgram.stages heapTyped argumentsTyped body.sound,
    result⟩

/-- Independent Source completion supplies a genuine body grade and native
fuel. The original strong root producer keeps the same causal result. -/
theorem program_has_sufficient_native_fuel_with_exit
    (atProgram : ProgramAtWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ outcome after) :
    ∃ sourceSize value finalStore finalMap finalWorld required,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after ∧
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit
        actual.fixture root inventory initial sourceSize none
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨size, body⟩ := RecursiveNamedCallBounds.BodyOutcome.has_size
    (RecursiveNamedProgramOutcomeMeaning.body_from_program caller executed)
  obtain ⟨value, finalStore, finalMap, finalWorld, required, completes, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission.preserves_root
      actual root inventory initial checkpoint atProgram.root body
  exact ⟨size, value, finalStore, finalMap, finalWorld, required, body, completes, result⟩

/-- The actual successful export identifies the same Source Word. The low
observation is only a projection; the returned result still retains its exit. -/
theorem public_succeeded_reflects_program_with_exit
    (atProgram : ProgramAtWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {fuel : Nat} {completion : Completion actual.artifact}
    (resumed : checkpoint.ResumeAt fuel boundaryFuel (.succeeded completion)) :
    ∃ sourceSize nativeChildSize word after finalStore finalMap finalWorld,
      completion.value = .word word ∧ completion.sourceType = .word ∧
      completion.session.NativeAt (finalStore.map Core.Value.type) finalStore ∧
      EvaluationSize nativeChildSize (DataPatternValues.packValues ([] : List Core.Value) :: initial.capture.captured)
        store (caller.code.rename initial.capture.embedding.lift) (.inRight .word (.word word)) finalStore ∧
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] (.value (.word word)) after ∧
      Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ (.value (.word word)) after ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit
        actual.fixture root inventory initial sourceSize (some nativeChildSize)
        (.value (.word word)) after (.inRight .word (.word word)) finalStore finalMap finalWorld := by
  obtain ⟨generation, native, finalStore, done, succeeded⟩ := resumed.succeeded
  obtain ⟨sourceSize, nativeChildSize, outcome, after, finalMap, finalWorld, child, body, executed, result⟩ :=
    native_completed_reflects_program_with_exit actual root inventory initial checkpoint atProgram done
  have observed := SourceCoreChosenOrdinaryAcceptedPublicResultObservation.observe
    actual.fixture root inventory initial atProgram.bootstrap
    (SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit.forget
      actual.fixture root inventory initial result)
  have decoded : ∃ payload, LanguageResult.decode? native = some (.succeeded payload) := by
    obtain ⟨_, payload, _, _, _, decoded, _⟩ := succeeded
    exact ⟨payload, decoded⟩
  obtain ⟨word, sourceEq, nativeEq⟩ :
      ∃ word, outcome = .value (.word word) ∧ native = .inRight .word (.word word) := by
    cases observed with
    | word word => exact ⟨word, rfl, rfl⟩
    | fault related =>
      obtain ⟨payload, impossible⟩ := decoded
      simp [LanguageResult.decode?] at impossible
  subst outcome
  subst native
  exact ⟨sourceSize, nativeChildSize, word, after, finalStore, finalMap, finalWorld,
    succeeded.word_value atProgram.requested, succeeded.source_type atProgram.requested,
    succeeded.native_at.2, child, body, executed, result⟩

/-- A Source Word crosses the same positive export boundary at sufficient
native fuel. The genuine Source grade and full strong result are retained. -/
theorem program_word_preserved_with_exit
    (atProgram : ProgramAtWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    (positive : 0 < boundaryFuel) {word : Word} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ (.value (.word word)) after) :
    ∃ sourceSize finalStore finalMap finalWorld required,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] (.value (.word word)) after ∧
      (∀ fuel, required ≤ fuel → ∀ outcome, checkpoint.ResumeAt fuel boundaryFuel outcome →
        ∃ completion, outcome = .succeeded completion ∧ completion.value = .word word) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit
        actual.fixture root inventory initial sourceSize none
        (.value (.word word)) after (.inRight .word (.word word)) finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, native, finalStore, finalMap, finalWorld, required, body, completes, result⟩ :=
    program_has_sufficient_native_fuel_with_exit actual root inventory initial checkpoint atProgram executed
  have observed := SourceCoreChosenOrdinaryAcceptedPublicResultObservation.observe
    actual.fixture root inventory initial atProgram.bootstrap
    (SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit.forget
      actual.fixture root inventory initial result)
  have nativeEq := (observed.word_iff word).mp rfl
  subst native
  exact ⟨sourceSize, finalStore, finalMap, finalWorld, required, body,
    fun fuel enough outcome resumed => resumed.word_succeeded
      (completes fuel enough) atProgram.requested positive, result⟩

/-- The existing public run's erased receipts supply one strong factory and
one reflection. No new collector, start or resume action is introduced. -/
theorem public_run_succeeded_reflects_program_with_exit
    (given : SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.PublicRun)
    (faults : FunctionCalls.FaultRep) {completion : Completion given.actual.artifact}
    (succeeded : given.outcome = .succeeded completion) :
    ∃ header : ActualHeader given.actual.fixture,
    ∃ selectedCompilation : Compilation given.actual.fixture.packet.compiled.indexed header.named
      (effectiveDiagnostics given.actual.fixture.packet.compiled given.actual.fixture.packet.diagnostics)
      given.actual.fixture.packet.namedCode,
    ∃ selectedRoot : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root
      given.actual.fixture header selectedCompilation,
    ∃ firstWorld firstStore,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt given.actual.fixture header
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions given.actual.fixture selectedRoot
        given.static.inventory (registry given.actual) faults)
      (registry given.actual) firstWorld firstStore,
      ProgramAtWithExit (boundaryFuel := SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.boundaryBudget)
        given.actual selectedRoot given.static.inventory first given.checkpoint ∧
      given.actual.session.NativeAt firstWorld firstStore ∧
      ∃ sourceSize nativeChildSize word after finalStore finalMap finalWorld,
        completion.value = .word word ∧ completion.sourceType = .word ∧
        completion.session.NativeAt (finalStore.map Core.Value.type) finalStore ∧
        EvaluationSize nativeChildSize (DataPatternValues.packValues ([] : List Core.Value) :: first.capture.captured)
          firstStore (header.code.rename first.capture.embedding.lift) (.inRight .word (.word word)) finalStore ∧
        RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked given.actual.fixture.packet.compiled.sourceProgram)
          sourceSize header.sourceBody header.function.evidence ⟨[]⟩ [] (.value (.word word)) after ∧
        Dynamic.ProgramOutcome (Program.ofChecked given.actual.fixture.packet.compiled.sourceProgram)
          (RecursiveNamedProgramEntrySource.entry header []) ⟨[]⟩ (.value (.word word)) after ∧
        SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit
          given.actual.fixture selectedRoot given.static.inventory first sourceSize (some nativeChildSize)
          (.value (.word word)) after (.inRight .word (.word word)) finalStore finalMap finalWorld := by
  obtain ⟨header, selectedCompilation, selectedRoot, firstWorld, firstStore, first, native, atProgram⟩ :=
    at_started (faults := faults) given.actual given.checkpoint given.static given.accepted
  have resumed : given.checkpoint.ResumeAt
      SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.nativeFuel
      SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.boundaryBudget (.succeeded completion) := by
    rw [← succeeded]
    exact given.resumed
  exact ⟨header, selectedCompilation, selectedRoot, firstWorld, firstStore, first, atProgram, native,
    public_succeeded_reflects_program_with_exit
      given.actual selectedRoot given.static.inventory first given.checkpoint atProgram resumed⟩

end Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramOutcomeWithExit
end
