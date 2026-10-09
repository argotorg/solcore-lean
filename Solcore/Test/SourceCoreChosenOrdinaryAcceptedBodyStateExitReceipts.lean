import Solcore.Test.SourceCoreChosenOrdinaryAcceptedBodyStatePorts
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedHeaderRuntimeEvidence
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedOuterBodyLexicalExit

/-! The genuine initialized body exit is retained at its original named
parameter receipt. The full lexical administrative context comes from that
same BodyState, independently of the shorter creator capture. Source and
native ports retain the original returned pool, effects and post admission. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts
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

include runtime prefixZero in
/-- The actual body evaluation, lexical exit and admission retain one returned
state. Only the genuine Header and empty parameter environment are transported. -/
private theorem result_at_receipt {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (evaluated : Evaluates receipt.body.actualBody receipt.body.store
      (caller.body.rename receipt.body.embedding) value finalStore)
    (post : SourceCoreChosenOrdinaryAcceptedOuterBodyLexicalExit.BodyResultWithExit
      (fixture := fixture) (inventory := inventory) (root := root) (registry := registry) (faults := faults)
      (owner := owner) (canonical := receipt.body.canonical) (initial := receipt.reached)
      (packet := input_packet fixture runtime inventory root owner prefixZero receipt)
      (administrative := SourceCoreCompatibleCatalog.packTypes (caller.bindings.map Prod.snd) :: receipt.administrative)
      outcome after value finalStore finalMap finalWorld) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.ResultAt receipt (faults := faults)
      outcome after value finalStore finalMap finalWorld := by
  obtain ⟨⟨represented, heaps, maps, worlds, frame, metadata, returned, related, admitted⟩, exited⟩ := post
  refine ⟨evaluated, represented, heaps, maps, worlds, frame, metadata, ?_, returned.val, related, ?_⟩
  · simpa only [CallableIndexedAmbient.ambient_definitions, SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt,
      (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1]
      using exited
  · refine ⟨admitted.rows, ?_⟩
    intro sourceValue same
    simpa only [runtime.toHeaderAt.context] using admitted.successful sourceValue same

variable (extension : SourceCoreRawMetadata.Extends
  (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- One genuine outer body proof supplies the existing strong Source receipt
contract, including its actual stopping context and same returned admission. -/
theorem source_preserves_at_receipt (size : Nat) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.PreservesAt receipt (faults := faults) size := by
  intro outcome after trace
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
    SourceCoreChosenOrdinaryAcceptedOuterBodyLexicalExit.preserves_body_with_exit fixture runtime.toHeaderAt shape typing checked inventory
      root chosen outer captured rfl owner receipt.reached packet extension observed
      receipt.body.heaps.runtime_hasTypes environments receipt.body.heaps
      (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.source_locals fixture runtime.toHeaderAt functions owner receipt)
      receipt.body.lookups reference receipt.body.state.read ready admitted runtime.evidence size originalTrace (Nat.le_refl size)
  exact ⟨value, finalStore, finalMap, finalWorld,
    result_at_receipt fixture runtime inventory root owner prefixZero receipt evaluated post⟩

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- One genuine native body child supplies an independent Source grade and the
existing strong receipt result at the same original input and final state. -/
theorem native_reflects_at_receipt (size : Nat) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.ReflectsAt receipt (faults := faults) size := by
  intro value finalStore completed
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
    SourceCoreChosenOrdinaryAcceptedOuterBodyLexicalExit.reflects_body_with_exit fixture runtime.toHeaderAt shape typing checked inventory
      root chosen outer captured rfl owner receipt.reached packet extension observed
      receipt.body.heaps.runtime_hasTypes environments receipt.body.heaps
      (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.source_locals fixture runtime.toHeaderAt functions owner receipt)
      receipt.body.lookups reference receipt.body.state.read ready admitted runtime.evidence size completed (Nat.le_refl size)
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld, ?_,
    result_at_receipt fixture runtime inventory root owner prefixZero receipt completed.sound post⟩
  simpa only [(SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1] using trace

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- Every strict Source body child uses its own original receipt. The supplied
prefix agreement is retained by the unchanged callback interface. -/
theorem source_bodies_for (budget : Nat) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
      (headers := headers) («functions» := functions) (owner := owner) (registry := registry) (faults := faults) caller budget := by
  intro initial argumentsPool arguments actualReceipt _agreement size _strict
  exact source_preserves_at_receipt fixture runtime shape typing checked inventory root chosen outer owner complete
    prefixZero actualReceipt extension size

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- Every strict native child retains the original prefix and saved restoration
indices while reflecting to its own independent Source grade. -/
theorem native_bodies_for (budget : Nat) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
      (headers := headers) («functions» := functions) (owner := owner) (registry := registry) (faults := faults) caller budget := by
  intro initial argumentsPool arguments actualReceipt prefixSize bodyStore value finalStore _prefix _prefixSmall _restored size _strict
  exact native_reflects_at_receipt fixture runtime shape typing checked inventory root chosen outer owner complete
    prefixZero actualReceipt extension size

end Tests.SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts
