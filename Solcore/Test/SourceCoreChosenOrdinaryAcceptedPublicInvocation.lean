import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicParameterEntry
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence

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
