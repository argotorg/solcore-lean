import Solcore.Test.SourceCoreChosenOrdinaryAcceptedBodyStatePorts
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedHeaderRuntimeEvidence
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedInitialBodyAdmission
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds

/-! The proved accepted body runs at the original named parameter receipt.
Its captures, native state, readiness and Source admission come from that same
BodyState. The public invocation ports retain its actual reached pool and all
returned rows, without a body execution law or whole-program typing premise. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  (runtime : SourceCoreChosenOrdinaryAcceptedHeaderRuntimeEvidence.RuntimeEvidence fixture caller)
  (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
  (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
  (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata fixture.packet)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)
  (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt fixture)
  {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := fixture.packet.compiled.indexed.ancestry)
    (values := .initial fixture.packet.compiled.compatible.checked)
    (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed) headers)
  (prefixZero : owner.key.capturePrefix = 0)
  {index : ProtectedStateTransition.Index} {argumentsPool : State headers keys index}
  {arguments : List Dynamic.Value}
  (receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
      (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
    owner argumentsPool caller arguments)

local notation "functions" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
  (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts
local notation "model" => CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions
local notation "protocol" => CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller
local notation "bridge" => CallableIndexedOwnedIndirectCallerProtocol.forget_slots
  (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)
local notation "baseBridge" => CallableIndexedOwnedIndirectCallerProtocol.of_legacy
  (CallableIndexedOwnedCallerProtocol.base (headers := headers) (keys := keys))

/-- Only the proof of the empty Source environment is transported. Every
native capture field comes from the original actual parameter BodyState. -/
def creation_capture : Captures fixture.packet.compiled.indexed receipt.body.mapping receipt.body.world
    (initialScope fixture.packet) (chosen.chosen.formation.function []).captured receipt.body.actualBody := by
  let captured := SourceCoreChosenOrdinaryAcceptedBodyStatePorts.captures_at_entry
    fixture functions owner receipt complete prefixZero runtime.globals
  exact {
    administrative := captured.administrative
    canonical := captured.canonical
    actualContext := captured.actualContext
    embedding := captured.embedding
    represented := by
      simpa only [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt,
        (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1,
        CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.function, CallableIndexedLambdaGeneration.closure]
        using captured.represented
    agrees := captured.agrees
    respects := by
      simpa only [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using captured.respects
    typed := captured.typed }

include runtime prefixZero in
/-- The packet and the pool are those of the same original receipt. -/
theorem input_packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller
    ⟨initialScope fixture.packet, receipt.body.mapping, receipt.body.world,
      receipt.body.heap, receipt.body.store, receipt.body.canonical⟩ receipt.reached := by
  let original := receipt.packet prefixZero runtime.globals
  refine ⟨?_, ?_, ?_, original.carried⟩
  · simpa only [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using original.globals
  · simpa only [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using original.reference
  · simpa only [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using original.bundle

/-- The complete actual body post retains its returned original pool and
successful raw value/heap typing, as well as all native cumulative effects. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  FunctionCalls.ResultRepresents model finalMap finalWorld caller.function.resultType caller.output faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends receipt.body.mapping finalMap ∧ WorldExtends receipt.body.world finalWorld ∧
  AdministrativePreserved receipt.body.mapping receipt.body.store finalMap finalStore ∧
  Dynamic.HeapMetadataExtend receipt.body.heap after ∧
  ∃ returned : State headers keys ⟨caller.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      finalMap, finalWorld, after, finalStore, receipt.body.canonical⟩,
    Relates receipt.reached returned ∧ PostAdmission baseBridge caller.context caller.function.resultType outcome returned

include runtime prefixZero in
private theorem post_at_receipt {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (post : SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds.BodyResultAt
      (fixture := fixture) (inventory := inventory) (root := root) (registry := registry) (faults := faults)
      (owner := owner) (canonical := receipt.body.canonical) (initial := receipt.reached) (packet := input_packet fixture runtime inventory root owner prefixZero receipt)
      outcome after value finalStore finalMap finalWorld) :
    ResultAt (fixture := fixture) (inventory := inventory) (root := root) (owner := owner) (receipt := receipt) outcome after value finalStore finalMap finalWorld := by
  obtain ⟨represented, heaps, maps, worlds, frame, metadata, returned, related, admitted⟩ := post
  refine ⟨represented, heaps, maps, worlds, frame, metadata, returned.val, related, ?_⟩
  refine ⟨admitted.rows, ?_⟩
  intro sourceValue same
  simpa only [runtime.toHeaderAt.context] using admitted.successful sourceValue same

variable (extension : SourceCoreRawMetadata.Extends
  (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- Apply the proved body once at the real parameter receipt, deriving every
capture, frame, readiness and admission port from that same actual input. -/
theorem preserves_at_receipt (budget : Nat) {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size caller.function caller.context receipt.body.environment receipt.body.heap outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates receipt.body.actualBody receipt.body.store (caller.body.rename receipt.body.embedding) value finalStore ∧
      ResultAt (fixture := fixture) (inventory := inventory) (root := root) (owner := owner) (receipt := receipt) outcome after value finalStore finalMap finalWorld := by
  let captured := creation_capture fixture runtime inventory root chosen owner complete prefixZero receipt
  let packet := input_packet fixture runtime inventory root owner prefixZero receipt
  let first : (protocol).State ⟨initialScope fixture.packet, receipt.body.mapping, receipt.body.world,
    receipt.body.heap, receipt.body.store, receipt.body.canonical⟩ := ⟨receipt.reached, packet⟩
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked) (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      headers owner.key.locations 1 (initialScope fixture.packet) captured.canonical owner.key.frameLocation := by
    have original := SourceCoreChosenOrdinaryAcceptedBodyStatePorts.captured_globals fixture functions owner receipt complete prefixZero runtime.globals
    simpa only [captured, creation_capture, SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using original
  have ready : (CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) owner caller model).Ready
      first receipt.frameLocation (.state receipt.index) := by
    apply CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner caller model receipt.stable_owner
    exact receipt.body.state.read
  have admitted : Admission bridge (runtimeContext fixture.packet) first :=
    ⟨SourceCoreChosenOrdinaryAcceptedBodyStatePorts.source_heap_typed fixture runtime.toHeaderAt functions owner receipt, receipt.rows⟩
  have environments := receipt.body.environments
  rw [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt,
    (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1] at environments
  have reference := receipt.body.reference
  have scopeLength : (initialScope fixture.packet).length = caller.bindings.length := by
    rw [← SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt, List.length_map, List.length_reverse]
  rw [← scopeLength, runtime.globals] at reference
  have originalTrace := trace
  rw [(SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1] at originalTrace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, post⟩ :=
    SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds.preserves_body fixture runtime.toHeaderAt shape typing checked inventory
      root chosen outer captured rfl owner receipt.reached packet extension
      observed
      receipt.body.heaps.runtime_hasTypes environments receipt.body.heaps
      (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.source_locals fixture runtime.toHeaderAt functions owner receipt)
      receipt.body.lookups reference receipt.body.state.read ready admitted runtime.evidence budget originalTrace within
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, post_at_receipt fixture runtime inventory root owner prefixZero receipt post⟩

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- The genuine native body child reflects to an independent Source grade at
that same parameter state; no Source body execution is supplied as an input. -/
theorem reflects_at_receipt (budget : Nat) {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size receipt.body.actualBody receipt.body.store
      (caller.body.rename receipt.body.embedding) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
        sourceSize caller.function caller.context receipt.body.environment receipt.body.heap outcome after ∧
      ResultAt (fixture := fixture) (inventory := inventory) (root := root) (owner := owner) (receipt := receipt) outcome after value finalStore finalMap finalWorld := by
  let captured := creation_capture fixture runtime inventory root chosen owner complete prefixZero receipt
  let packet := input_packet fixture runtime inventory root owner prefixZero receipt
  let first : (protocol).State ⟨initialScope fixture.packet, receipt.body.mapping, receipt.body.world,
    receipt.body.heap, receipt.body.store, receipt.body.canonical⟩ := ⟨receipt.reached, packet⟩
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked) (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      headers owner.key.locations 1 (initialScope fixture.packet) captured.canonical owner.key.frameLocation := by
    have original := SourceCoreChosenOrdinaryAcceptedBodyStatePorts.captured_globals fixture functions owner receipt complete prefixZero runtime.globals
    simpa only [captured, creation_capture, SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using original
  have ready : (CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) owner caller model).Ready
      first receipt.frameLocation (.state receipt.index) := by
    apply CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner caller model receipt.stable_owner
    exact receipt.body.state.read
  have admitted : Admission bridge (runtimeContext fixture.packet) first :=
    ⟨SourceCoreChosenOrdinaryAcceptedBodyStatePorts.source_heap_typed fixture runtime.toHeaderAt functions owner receipt, receipt.rows⟩
  have environments := receipt.body.environments
  rw [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt,
    (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1] at environments
  have reference := receipt.body.reference
  have scopeLength : (initialScope fixture.packet).length = caller.bindings.length := by
    rw [← SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt, List.length_map, List.length_reverse]
  rw [← scopeLength, runtime.globals] at reference
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, post⟩ :=
    SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds.reflects_body fixture runtime.toHeaderAt shape typing checked inventory
      root chosen outer captured rfl owner receipt.reached packet extension
      observed
      receipt.body.heaps.runtime_hasTypes environments receipt.body.heaps
      (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.source_locals fixture runtime.toHeaderAt functions owner receipt)
      receipt.body.lookups reference receipt.body.state.read ready admitted runtime.evidence budget completed within
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld, ?_, post_at_receipt fixture runtime inventory root owner prefixZero receipt post⟩
  simpa only [(SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1] using trace

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- The existing Source invocation interface is satisfied at the actual receipt. -/
theorem source_body_at (size : Nat) :
    CallableIndexedOwnedInvocationBounds.SourceBodyAt (faults := faults) receipt.body receipt.reached size := by
  intro outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, returned, related, _admitted⟩ :=
    preserves_at_receipt fixture runtime shape typing checked inventory root chosen outer owner complete prefixZero receipt extension size trace (Nat.le_refl size)
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, returned, related⟩

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- The existing native invocation interface retains the independent Source cost. -/
theorem native_body_at (size : Nat) :
    CallableIndexedOwnedInvocationBounds.NativeBodyAt (faults := faults) receipt.body receipt.reached size := by
  intro value finalStore completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, returned, related, _admitted⟩ :=
    reflects_at_receipt fixture runtime shape typing checked inventory root chosen outer owner complete prefixZero receipt extension size completed (Nat.le_refl size)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, returned, related⟩

end Tests.SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence
