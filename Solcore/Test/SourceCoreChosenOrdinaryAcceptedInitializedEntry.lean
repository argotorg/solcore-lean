import Solcore.Test.SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedInitializerAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedAllocationState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCallerProtocol

/-! One real formation and one marked allocation connect the accepted lambda
initializer to its actual admitted parent entry. The original formation history
is retained through allocation; the parent index uses the same extended capture.
Initial heap, frame, capture, all-row admission and allocator readiness remain
genuine inputs. No body execution law is an input. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedInitializedEntry
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  (atHeader : HeaderAt fixture caller)
  (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
  (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
  (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata fixture.packet)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)
  (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt fixture)

include atHeader typing in
/-- The Source binder type comes from the same original lambda occurrence. -/
theorem binder_type : fixture.graph.binder.scheme.body =
    FunctionValues.sourceType (chosen.chosen.formation.function []) := by
  have found := chosen.chosen.formation.produced.site.code.sourceFound
  rw [chosen.chosen.formation.produced.identifier] at found
  change (source caller.named).lookupExpression? (expressionId fixture.packet 1) = some _ at found
  have foundFixture : (source fixture.packet.named).lookupExpression? (expressionId fixture.packet 1) = some chosen.chosen.formation.produced.site.code.sourceNode := by
    simpa only [atHeader.named] using found
  have sameNode := Option.some.inj (foundFixture.symm.trans fixture.graph.lambdaFound)
  have raw := chosen.chosen.formation.sourceType
  rw [sameNode] at raw
  exact (SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.raw_initializer_type fixture typing).symm.trans raw

include outer in
/-- The accepted initializer payload is the original checked callable type. -/
theorem payload_type : fixture.calls.payload = CallableContract.functionType
    (chosen.chosen.formation.code []).receipt.parameterCore
    (chosen.chosen.formation.code []).receipt.resultCore := by
  have emitted := chosen.chosen.formation.produced.emitted
  have native := RecursiveNamedLambdaFormationHeads.site_native_type (values := .initial fixture.packet.compiled.compatible.checked) (caller := caller) chosen.chosen.formation.produced.site
  exact outer.initializerType.symm.trans ((congrArg SourceCoreBasic.LoweredExpr.type emitted).symm.trans native)

variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures fixture.packet.compiled.indexed mapping world (initialScope fixture.packet)
    (chosen.chosen.formation.function []).captured actual)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial fixture.packet.compiled.compatible.checked) caller)

/-- Recapture retains the actual accepted initializer expression and renaming. -/
theorem initializer_expression :
    ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext).code.lowered.expression.rename
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext).captured.embedding) =
      fixture.calls.initializer.expression.rename captured.embedding := by
  exact congrArg (fun lowered : SourceCoreBasic.LoweredExpr => lowered.expression.rename captured.embedding)
    chosen.chosen.formation.produced.emitted

/-- The extended index is exactly the parent index with the same capture.
Only map/world proofs change; formation history is not reconstructed. -/
theorem index_after_allocation {nextMap : LocationMap} {nextWorld : StoreTyping}
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    CallableIndexedOwnedChosenOrdinaryStoredMembers.extendIndex
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext) maps worlds =
    CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] (captured.extend maps worlds) prefixContext := by
  rfl

local notation "i0" => CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext
local notation "functions" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
  (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts
local notation "model" => CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions
local notation "frame" => fixture.packet.compiled.indexed.ancestry.layout.frame

variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {administrative : Core.Context} {canonical : Environment} {before after : Dynamic.Heap} {store : Store}
  {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
  (initial : State headers keys ⟨initialScope fixture.packet, mapping, world, before, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)

local notation "history0" => CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at
  (i0).captured (i0).code (i0).support owner initial packet
local notation "closureValue" => value (i0).code (i0).captured.embedding (history0).native actual
local notation "producer" => CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) owner caller model
local notation "first" => (⟨initial, packet⟩ : (CallableIndexedOwnedNestedCanonicalState.protocol owner caller).State _)

/-- Every component is from one real initialized allocation at the original
formation history. The parent receives the exact reached state and all rows. -/
def InitializedAt : Prop :=
  ∃ allocationCapture,
    CallableIndexedAllocationCompletion.Captures (closureValue :: canonical)
      (SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.request fixture).references
      (initialScope fixture.packet) allocationCapture ∧
    RuntimeValueHasType world allocationCapture (SourceCoreSourceCells.captureType (initialScope fixture.packet))
      fixture.packet.compiled.indexed.layouts.definitions ∧
    let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
      SourceCoreHeapMarkers.markerValue outer.allocation.entry.layout allocationCapture, .inRight .unit closureValue]
    let nextWorld := world ++ [(frame).type, outer.allocation.entry.layout.type, OptionalCell.cellType fixture.calls.payload]
    let nextMap := mapping ++ [store.length + 2]
    let nextRef := Value.cellRef (OptionalCell.cellType fixture.calls.payload) (store.length + 2)
    Evaluates (closureValue :: actual) store (outer.annotation.expression.rename captured.embedding.lift) nextRef nextStore ∧
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog fixture.packet.compiled.compatible.checked.catalog)
      nextMap nextWorld administrative (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture)
      [(fixture.graph.binder.id, location)] (nextRef :: canonical) fixture.packet.compiled.indexed.layouts.definitions ∧
    CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry functions nextMap nextWorld after nextStore ∧
    Dynamic.EnvironmentAgrees after (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture).locals
      [(fixture.graph.binder.id, location)] ∧
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) captured.embedding).lift
      (nextRef :: canonical) (nextRef :: closureValue :: actual) ∧
    RuntimeEnvironmentHasTypes nextWorld (nextRef :: closureValue :: actual)
      (OptionalCell.referenceType fixture.calls.payload :: fixture.calls.payload :: captured.actualContext)
      fixture.packet.compiled.indexed.layouts.definitions ∧
    (nextRef :: canonical)[(SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture).length + 1 +
      fixture.packet.compiled.indexed.base.globals.length]? = some (.cellRef (frame).type contextLocation) ∧
    nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
    AdministrativePreserved mapping store nextMap nextStore ∧
    ∃ (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld),
      Dynamic.HeapMetadataExtend before after ∧
      ReferenceRepresents nextMap nextWorld location (store.length + 2) fixture.calls.payload ∧
      CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenStoredAt root.root
        (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults
        (CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] (captured.extend maps worlds) prefixContext)
        history0 after nextStore location ∧
      ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol owner caller).State
          ⟨SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        (CallableIndexedOwnedNestedCanonicalState.protocol owner caller).Relates first reached ∧
        Relates initial reached.val ∧
        Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
          (CallableIndexedOwnedNestedCallerProtocol.carrier owner caller))
          (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) reached

include atHeader shape typing checked in
/-- The genuine Source initializer is formed once, then its actual marked
allocator runs once. Input captures, heap and every caller row stay explicit. -/
theorem initialized_entry
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram) headers owner.key.locations 1
      (initialScope fixture.packet) captured.canonical owner.key.frameLocation)
    (stored : RuntimeStoreHasTypes world store fixture.packet.compiled.indexed.layouts.definitions)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog fixture.packet.compiled.compatible.checked.catalog)
      mapping world administrative (initialScope fixture.packet) [] canonical fixture.packet.compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry functions
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before (runtimeContext fixture.packet).locals [])
    (agrees : EnvironmentsAgree captured.embedding canonical actual)
    (reference : canonical[(initialScope fixture.packet).length + 1 + fixture.packet.compiled.indexed.base.globals.length]? =
      some (.cellRef (frame).type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before fixture.graph.binder.scheme.body
      (some (.closure (i0).function)) location after)
    (ready : (producer).Ready first contextLocation native)
    (admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
      (CallableIndexedOwnedNestedCallerProtocol.carrier owner caller)) (runtimeContext fixture.packet) first) :
    Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (runtimeContext fixture.packet) [] (source caller.named) [] before
      (expressionId fixture.packet 1) (.closure (i0).function) before ∧
    Evaluates actual store (fixture.calls.initializer.expression.rename captured.embedding)
      (.inRight .word closureValue) store ∧
    (∀ result finalStore, Evaluates actual store (fixture.calls.initializer.expression.rename captured.embedding) result finalStore →
      result = .inRight .word closureValue ∧ finalStore = store) ∧
    InitializedAt fixture inventory root chosen outer captured prefixContext owner initial packet
      (registry := registry) (faults := faults) (administrative := administrative) (after := after)
      (contextLocation := contextLocation) (native := native) (location := location) := by
  obtain ⟨sourceTrace, evaluated, _represented, determined, _formed, member⟩ :=
    CallableIndexedOwnedChosenOrdinaryStoredMembers.formation_chosen_member (registry := registry) (faults := faults) (heap := before) root.root
      (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) chosen.chosen chosen.factory []
      captured prefixContext owner initial packet inventory.contracts observed stored
  have valueTyped := SourceCoreChosenOrdinaryAcceptedInitializerAdmission.receipt_value_has_type
    fixture shape [] atHeader chosen.chosen locals
  rw [SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.raw_initializer_type fixture typing] at valueTyped
  have mono : fixture.graph.binder.scheme.quantified = [] := by rw [typing.scheme]; rfl
  have ordinary : (source fixture.packet.named).inputs.any (fun input => decide (input.id = fixture.graph.binder.id)) = false := by
    rw [checked.inputs]; rfl
  have allocationPost := CallableIndexedOwnedChosenOrdinaryInitializedAllocationState.allocate_initialized
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) inventory.contracts
    (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (CallableIndexedOwnedNestedCallerProtocol.carrier owner caller))
    rfl (CallableIndexedAmbient.frame_registered fixture.packet.compiled.indexed) producer mono typing.extended ordinary
    outer.allocation outer.annotation outer.same (binder_type fixture atHeader typing root chosen)
    (payload_type fixture root chosen outer) member valueTyped environments heaps locals agrees captured.typed
    reference read allocated first ready admitted
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [CallableIndexedOwnedChosenOrdinaryFormedMembers.index,
      CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.function,
      CallableIndexedLambdaGeneration.closure, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.code,
      RecursiveNamedLambdaFormationHeads.recaptureCode, chosen.chosen.formation.produced.identifier]
      using sourceTrace
  · simpa only [initializer_expression fixture root chosen captured prefixContext] using evaluated
  · simpa only [initializer_expression fixture root chosen captured prefixContext] using determined
  · exact allocationPost

end Tests.SourceCoreChosenOrdinaryAcceptedInitializedEntry
