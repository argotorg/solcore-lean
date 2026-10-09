import Solcore.Test.SourceCoreChosenOrdinaryAcceptedInitializedEntry
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedHeaderEvidence

/-! The accepted outer body uses one original formation and one initialized
allocation. Its parent executes at that same admitted post. Complete value and
fault results retain cumulative effects and the actual restored caller pool.
Reflection constructs an independent Source body from the genuine native child
and uses whole-body determinism to identify its final value and store. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds
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

include atHeader shape typing in
/-- The original body grade contains the actual parent outcome and Source
allocation. Other function control outcomes are excluded by the two statements. -/
theorem source_parent_at_body (evidence : caller.function.evidence = [])
    {size : Nat} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size caller.function caller.context [] before outcome after) :
    ∃ parentSize location allocated,
      Dynamic.Heap.Allocates before fixture.graph.binder.scheme.body
        (some (.closure (chosen.chosen.formation.function []))) location allocated ∧
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
        parentSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) []
        (source fixture.packet.named) [(fixture.graph.binder.id, location)] allocated
        (expressionId fixture.packet 5) outcome after ∧ parentSize < size := by
  have invert {finalContext control} (body : RecursiveNamedLoopContracts.ExecutesAt size true
      (Program.ofChecked fixture.packet.compiled.sourceProgram) (runtimeContext fixture.packet) []
      (source fixture.packet.named) [] before [statementId fixture.packet 0, statementId fixture.packet 4]
      finalContext control after) := SourceCoreChosenOrdinaryAcceptedOuterBodyBounds.source_parent_at_body
        fixture shape typing body
  have closureEq := SourceCoreChosenOrdinaryAcceptedInitializerAdmission.receipt_function
    fixture [] atHeader chosen.chosen
  cases trace with
  | returned trace =>
    have body : RecursiveNamedLoopContracts.ExecutesAt size true _ _ _ _ _ _ _ _ _ _ :=
      .control (by simpa only [atHeader.context, atHeader.source, atHeader.statements, evidence] using trace)
    obtain ⟨_, _initializerSize, parentSize, location, allocated, parentOutcome, _initializer,
      allocation, parent, sameControl, _initializerSmall, parentSmall⟩ := invert body
    rw [← closureEq] at allocation
    cases parentOutcome with
    | value value => cases sameControl; exact ⟨parentSize, location, allocated, allocation, parent, parentSmall⟩
    | fault _ => cases sameControl
  | fault trace =>
    have body : RecursiveNamedLoopContracts.ExecutesAt size true _ _ _ _ _ _ _ _ _ _ :=
      .fault (by simpa only [atHeader.context, atHeader.source, atHeader.statements, evidence] using trace)
    obtain ⟨_, _initializerSize, parentSize, location, allocated, parentOutcome, _initializer,
      allocation, parent, sameControl, _initializerSmall, parentSmall⟩ := invert body
    rw [← closureEq] at allocation
    cases parentOutcome with
    | value _ => cases sameControl
    | fault reason => cases sameControl; exact ⟨parentSize, location, allocated, allocation, parent, parentSmall⟩
  | unit same _ => rw [typing.header_result atHeader] at same; cases same
  | escaped trace escape =>
    have body : RecursiveNamedLoopContracts.ExecutesAt size true _ _ _ _ _ _ _ _ _ _ :=
      .control (by simpa only [atHeader.context, atHeader.source, atHeader.statements, evidence] using trace)
    obtain ⟨_, _initializerSize, _parentSize, _location, _allocated, parentOutcome, _initializer,
      _allocation, _parent, sameControl, _initializerSmall, _parentSmall⟩ := invert body
    rcases escape with ⟨_, same⟩ | ⟨_, same⟩ <;> cases parentOutcome <;> rw [same] at sameControl <;> cases sameControl

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
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {administrative : Core.Context} {canonical : Environment} {before : Dynamic.Heap} {store : Store}
  {contextLocation : Location} {native : NativeFrame}
  (initial : State headers keys ⟨initialScope fixture.packet, mapping, world, before, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)

local notation "functions" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
  (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts
local notation "model" => CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions
local notation "protocol" => CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller
local notation "bridge" => CallableIndexedOwnedIndirectCallerProtocol.forget_slots
  (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)
local notation "first" => (⟨initial, packet⟩ : (protocol).State _)

/-- The complete body result refers to its actual restored caller and all
rows. Successful outcomes also retain raw Source value and deep heap typing. -/
def BodyResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  FunctionCalls.ResultRepresents model finalMap finalWorld caller.function.resultType caller.output faults outcome result ∧
  CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ returned : (protocol).State ⟨initialScope fixture.packet, finalMap, finalWorld, after, finalStore, canonical⟩,
    (protocol).Relates first returned ∧ PostAdmission bridge (runtimeContext fixture.packet) caller.function.resultType outcome returned

include atHeader outer in
private theorem whole_of_parent {allocatedStore finalStore : Store} {reference closure result : Value}
    {finalMap : LocationMap} {finalWorld : StoreTyping} {outcome : Dynamic.ExpressionOutcome}
    (initializer : Evaluates actual store (fixture.calls.initializer.expression.rename captured.embedding)
      (.inRight .word closure) store)
    (allocation : Evaluates (closure :: actual) store (outer.annotation.expression.rename captured.embedding.lift)
      reference allocatedStore)
    (parent : Evaluates (reference :: closure :: actual) allocatedStore
      (fixture.calls.parent.expression.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) result finalStore)
    (represented : FunctionCalls.ResultRepresents model finalMap finalWorld chosen.parent.compiler.original.type
      fixture.calls.parent.type faults outcome result) :
    Evaluates actual store (caller.body.rename captured.embedding) result finalStore := by
  have nativeType := outer.parentType
  rw [nativeType] at represented
  cases represented with
  | value _ =>
    exact SourceCoreChosenOrdinaryAcceptedOuterBodyBounds.whole_from_parent_value
      fixture atHeader outer initializer allocation parent
  | fault _ =>
    exact SourceCoreChosenOrdinaryAcceptedOuterBodyBounds.whole_from_parent_fault
      fixture atHeader outer initializer allocation parent

include atHeader typing outer in
/-- Scope restoration keeps the parent's actual pool. Cumulative effects and
raw admission are transported from that same returned witness. -/
private theorem body_post_of_parent {allocatedMap finalMap : LocationMap} {allocatedWorld finalWorld : StoreTyping}
    {allocated after : Dynamic.Heap} {allocatedStore finalStore : Store} {reference result : Value}
    {outcome : Dynamic.ExpressionOutcome}
    (reached : (protocol).State ⟨SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture,
      allocatedMap, allocatedWorld, allocated, allocatedStore, reference :: canonical⟩)
    (related : (protocol).Relates first reached)
    (maps : LocationMap.Extends mapping allocatedMap) (worlds : WorldExtends world allocatedWorld)
    (frame : AdministrativePreserved mapping store allocatedMap allocatedStore)
    (metadata : Dynamic.HeapMetadataExtend before allocated)
    (post : CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt
      (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) (registry := registry) (faults := faults)
      bridge functions chosen.parent.compiler reached outcome after result finalStore finalMap finalWorld) :
    BodyResultAt (fixture := fixture) (inventory := inventory) (root := root) (registry := registry) (faults := faults) (owner := owner)
      (initial := initial) (packet := packet) outcome after result finalStore finalMap finalWorld := by
  obtain ⟨represented, heaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, returnedRelated, admitted⟩ := post
  have rawType : chosen.parent.compiler.original.type = caller.function.resultType := by
    rw [chosen.parent.original, fixture.graph.parentType, typing.header_result atHeader]
  have nativeType : fixture.calls.parent.type = caller.output := outer.parentType.trans (by simpa only [atHeader.named] using caller.resultType)
  have runtimeAdmission := SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction.post_admission_at_runtime
    fixture typing bridge returned admitted
  let restored := (CallableIndexedOwnedNestedCanonicalState.bindings (headers := headers) owner caller).restore (index := ⟨initialScope fixture.packet, finalMap, finalWorld, after, finalStore, canonical⟩)
    (id := fixture.graph.binder.id) (type := fixture.calls.payload) (value := reference) returned
  refine ⟨?_, heaps, maps.trans finalMaps, worlds.trans finalWorlds, frame.trans finalFrame,
    metadata.trans finalMetadata, restored, ?_, ?_⟩
  · simpa only [rawType, nativeType] using represented
  · have restoredRelated : (protocol).Relates returned restored :=
      (CallableIndexedOwnedNestedCanonicalState.bindings owner caller).restore_related
        (index := ⟨initialScope fixture.packet, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := fixture.graph.binder.id) (type := fixture.calls.payload) (value := reference) returned
    exact (protocol).trans related ((protocol).trans returnedRelated restoredRelated)
  · refine ⟨runtimeAdmission.rows, ?_⟩
    intro value same
    simpa only [rawType] using runtimeAdmission.successful value same

variable
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
    (values := .initial fixture.packet.compiled.compatible.checked) (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
    headers owner.key.locations 1 (initialScope fixture.packet) captured.canonical owner.key.frameLocation)
  (stored : RuntimeStoreHasTypes world store fixture.packet.compiled.indexed.layouts.definitions)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog fixture.packet.compiled.compatible.checked.catalog)
    mapping world administrative (initialScope fixture.packet) [] canonical fixture.packet.compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
      headers keys registry faults inventory.contracts) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before (runtimeContext fixture.packet).locals [])
  (agrees : EnvironmentsAgree captured.embedding canonical actual)
  (reference : canonical[(initialScope fixture.packet).length + 1 + fixture.packet.compiled.indexed.base.globals.length]? =
    some (.cellRef fixture.packet.compiled.indexed.ancestry.layout.frame.type contextLocation))
  (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode fixture.packet.compiled.indexed.ancestry.layout.frame native))
  (ready : (CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) owner caller
    (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
        headers keys registry faults inventory.contracts))).Ready ⟨initial, packet⟩ contextLocation native)
  (admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedNestedCallerProtocol.carrier owner caller)) (runtimeContext fixture.packet) ⟨initial, packet⟩)

include atHeader shape typing checked outer prefixContext extension observed stored environments heaps locals agrees reference read ready admitted in
/-- The genuine complete Source body constructs its initialized parent entry
once and preserves its actual whole result, effects and restored admission. -/
theorem preserves_body (evidence : caller.function.evidence = []) (budget : Nat)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size caller.function caller.context [] before outcome after) (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates actual store (caller.body.rename captured.embedding) result finalStore ∧
      BodyResultAt (fixture := fixture) (inventory := inventory) (root := root) (registry := registry) (faults := faults) (owner := owner)
        (initial := initial) (packet := packet) outcome after result finalStore finalMap finalWorld := by
  obtain ⟨parentSize, location, allocated, allocatedSource, parentTrace, parentSmall⟩ :=
    source_parent_at_body fixture atHeader shape typing root chosen evidence trace
  obtain ⟨_sourceInitializer, initializer, _determined, entry⟩ :=
    SourceCoreChosenOrdinaryAcceptedInitializedEntry.initialized_entry fixture atHeader shape typing checked inventory
      root chosen outer captured prefixContext owner initial packet observed stored environments heaps locals agrees
      reference read allocatedSource ready admitted
  obtain ⟨_allocationCapture, _captures, _captureTyped, allocation, parentEnvironments, parentHeaps, parentLocals,
    parentAgrees, parentTyped, _parentReference, _parentRead, allocationFrame, maps, worlds, allocationMetadata,
    _freshReference, actualStored, reached, related, _poolRelated, parentAdmission⟩ := entry
  have lookup : Dynamic.Environment.LooksUp [(fixture.graph.binder.id, location)] fixture.graph.binder.id location := .head
  obtain ⟨result, finalStore, finalMap, finalWorld, parent, post⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentPreservationBounds.preserves_parent_at_initialized
      fixture atHeader shape typing inventory root chosen bridge (captured.extend maps worlds) prefixContext
      _ [] extension parentEnvironments parentHeaps parentLocals parentAgrees parentTyped actualStored lookup reached
      parentAdmission budget parentTrace (Nat.le_trans (Nat.le_of_lt parentSmall) within)
  exact ⟨result, finalStore, finalMap, finalWorld,
    whole_of_parent (fixture := fixture) (atHeader := atHeader) (inventory := inventory)
      (root := root) (chosen := chosen) (outer := outer) (captured := captured) initializer allocation parent post.1,
    body_post_of_parent fixture atHeader typing inventory root chosen outer owner initial packet reached related maps worlds
      allocationFrame allocationMetadata post⟩

include atHeader shape typing checked outer prefixContext extension observed stored environments heaps locals agrees reference read ready admitted in
/-- Native completion constructs its Source allocation and body independently.
The authentic child budget is retained; whole determinism aligns its final post. -/
theorem reflects_body (evidence : caller.function.evidence = []) (budget : Nat)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (caller.body.rename captured.embedding) result finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
        sourceSize caller.function caller.context [] before outcome after ∧
      BodyResultAt (fixture := fixture) (inventory := inventory) (root := root) (registry := registry) (faults := faults) (owner := owner)
        (initial := initial) (packet := packet) outcome after result finalStore finalMap finalWorld := by
  have allocatedSource : Dynamic.Heap.Allocates before fixture.graph.binder.scheme.body
      (some (.closure (chosen.chosen.formation.function []))) _ _ := .append
  obtain ⟨_sourceInitializer, initializer, _determined, entry⟩ :=
    SourceCoreChosenOrdinaryAcceptedInitializedEntry.initialized_entry fixture atHeader shape typing checked inventory
      root chosen outer captured prefixContext owner initial packet observed stored environments heaps locals agrees
      reference read allocatedSource ready admitted
  obtain ⟨_allocationCapture, _captures, _captureTyped, allocation, parentEnvironments, parentHeaps, parentLocals,
    parentAgrees, parentTyped, _parentReference, _parentRead, allocationFrame, maps, worlds, allocationMetadata,
    _freshReference, actualStored, reached, related, _poolRelated, parentAdmission⟩ := entry
  obtain ⟨parentSize, parentResult, parentStore, parentWithin, parent⟩ :=
    SourceCoreChosenOrdinaryAcceptedOuterBodyBounds.parent_within_whole_budget fixture atHeader outer initializer allocation
      budget completed within
  have lookup : Dynamic.Environment.LooksUp [(fixture.graph.binder.id, ⟨before.cells.length⟩)]
      fixture.graph.binder.id ⟨before.cells.length⟩ := .head
  obtain ⟨parentSourceSize, outcome, after, finalMap, finalWorld, parentTrace, post⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentReflectionBounds.reflects_parent_at_initialized
      fixture atHeader shape typing inventory root chosen bridge (captured.extend maps worlds) prefixContext
      reached extension parentEnvironments parentHeaps parentLocals parentAgrees parentTyped actualStored lookup parentAdmission
      budget parent parentWithin
  have whole := whole_of_parent (fixture := fixture) (atHeader := atHeader) (inventory := inventory)
      (root := root) (chosen := chosen) (outer := outer) (captured := captured)
    initializer allocation parent.sound post.1
  obtain ⟨sameResult, sameStore⟩ := evaluation_deterministic whole completed.sound
  subst result
  subst finalStore
  obtain ⟨sourceSize, sourceBody, _sourceParentSmall⟩ :=
    SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction.body_trace_at_header fixture atHeader chosen.chosen typing
      evidence allocatedSource parentTrace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceBody,
    body_post_of_parent fixture atHeader typing inventory root chosen outer owner initial packet reached related maps worlds
      allocationFrame allocationMetadata post⟩

end Tests.SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds
