import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryFormedMembers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryStoredMembers

/-! Positive chosen-factory qualification stays at its literal ordinary index
through one actual formation and initialized allocation/write. Future mutation
transport uses the actual reads of the same optional payload. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredMembers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedMixedBodySiteInputs (ChosenFactory)
open CallableIndexedOwnedChosenOrdinaryFormedMembers (FactoryMember)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)


/-- These are the actual constructor fields at a known index and history.
No opaque value, stored relation or prior selection supplies the factory. -/
inductive ChosenAt (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (i : OrdinaryIndex compiled) (history : History i.code) : Prop where
  | ordinary (owner : OwnedKey keys) (factory : FactoryMember root expressionSyntax i)
      (origin : SourceOrigin i.support history)
      (prefixContext : i.captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) i.support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 i.scope i.captured.canonical owner.key.frameLocation)
      (referenceIndex : i.code.referenceIndex = i.scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType i.world (value i.code i.captured.embedding history.native i.capturedActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore)
        compiled.indexed.layouts.definitions) : ChosenAt headers keys registry faults i history

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {i : OrdinaryIndex compiled} {history : History i.code}

theorem ChosenAt.formed (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    CallableIndexedOwnedPreparedOrdinaryFormedMembers.FormedAt headers keys registry faults
      i.mapping i.world (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) := by
  cases member with
  | ordinary owner factory origin prefixContext globals referenceIndex typed =>
    exact .ordinary i owner history origin prefixContext globals referenceIndex typed

theorem ChosenAt.selection (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    CallableIndexedOwnedPreparedOrdinaryLambdaValues.Selection headers keys registry faults
      i.mapping i.world (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) := by
  cases member with
  | ordinary owner factory origin prefixContext globals referenceIndex typed =>
    exact .prepared_ordinary owner i.captured i.code history i.support origin prefixContext globals referenceIndex typed i.prepared

theorem ChosenAt.factory (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    FactoryMember root expressionSyntax i := by
  cases member with
  | ordinary owner factory origin prefixContext globals referenceIndex typed => exact factory

/-- The future index keeps the literal function, Code, Support and prepared body. -/
def extendIndex (i : OrdinaryIndex compiled) {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld) : OrdinaryIndex compiled := {
  function := i.function, mapping := futureMap, world := futureWorld, scope := i.scope
  capturedActual := i.capturedActual, captured := i.captured.extend maps worlds
  code := i.code, support := i.support, prepared := i.prepared }

theorem ChosenAt.extend (member : ChosenAt root expressionSyntax headers keys registry faults i history)
    {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld) :
    ChosenAt root expressionSyntax headers keys registry faults (extendIndex i maps worlds) history := by
  cases member with
  | ordinary owner factory origin prefixContext globals referenceIndex typed =>
    exact .ordinary owner (FactoryMember.extend root expressionSyntax factory maps worlds) origin prefixContext globals referenceIndex (typed.weaken worlds)

theorem ChosenAt.map_keys (member : ChosenAt root expressionSyntax headers keys registry faults i history)
    {futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys) :
    ChosenAt root expressionSyntax headers futureKeys registry faults i history := by
  cases member with
  | ordinary owner factory origin prefixContext globals referenceIndex typed =>
    have actualGlobals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers (embedding.map owner).key.locations 1 i.scope i.captured.canonical (embedding.map owner).key.frameLocation := by
      rw [embedding.same owner]
      exact globals
    exact .ordinary (embedding.map owner) factory origin prefixContext actualGlobals referenceIndex typed

/-- The real initialized cell and optional native read retain the known index. -/
def ChosenStoredAt (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (i : OrdinaryIndex compiled) (history : History i.code) (heap : Dynamic.Heap)
    (store : Store) (location : Dynamic.Location) : Prop :=
  ChosenAt root expressionSyntax headers keys registry faults i history ∧
  ∃ target, ReferenceRepresents i.mapping i.world location target
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) ∧
    Dynamic.Heap.Reads heap location ⟨FunctionValues.sourceType i.function, some (.closure i.function), none⟩ ∧
    store.read? target = some (.inRight .unit (value i.code i.captured.embedding history.native i.capturedActual))

theorem ChosenStoredAt.stored {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
    (stored : ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location) :
    CallableIndexedOwnedPreparedOrdinaryStoredMembers.StoredAt headers keys registry faults i.mapping i.world
      heap store location (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) :=
  ⟨stored.1.formed, stored.2⟩

theorem ChosenStoredAt.extend_with_reads {heap futureHeap : Dynamic.Heap} {store futureStore : Store}
    {location : Dynamic.Location} {futureMap : LocationMap} {futureWorld : StoreTyping}
    (stored : ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location)
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld)
    (reads : Dynamic.Heap.Reads futureHeap location ⟨FunctionValues.sourceType i.function, some (.closure i.function), none⟩)
    (nativeReads : ∀ target, ReferenceRepresents i.mapping i.world location target
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) →
      futureStore.read? target = some (.inRight .unit (value i.code i.captured.embedding history.native i.capturedActual))) :
    ChosenStoredAt root expressionSyntax headers keys registry faults (extendIndex i maps worlds) history futureHeap futureStore location := by
  obtain ⟨member, target, reference, _, _⟩ := stored
  exact ⟨ChosenAt.extend root expressionSyntax member maps worlds, target, reference.extend maps worlds, reads, nativeReads target reference⟩

theorem ChosenStoredAt.map_keys {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
    {futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys)
    (stored : ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location) :
    ChosenStoredAt root expressionSyntax headers futureKeys registry faults i history heap store location :=
  ⟨ChosenAt.map_keys root expressionSyntax stored.1 embedding, stored.2⟩
section Formation
variable {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    sourceContext evidence scope id lowered)
  (chosen : ChosenFactory root expressionSyntax receipt) (environment : Dynamic.Environment)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {actual canonical : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope (receipt.formation.function environment).captured actual)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

include chosen observed in
/-- The original formation producer runs once. The same complete tuple and
known formed member retain the positive chosen-factory companion. -/
theorem formation_chosen_member
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions) :
    let i := CallableIndexedOwnedChosenOrdinaryFormedMembers.index receipt environment captured prefixContext
    let history := CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at
      i.captured i.code i.support owner initial packet
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) i.function.context i.function.evidence
      i.function.source i.function.captured heap i.code.id (.closure i.function) heap ∧
    Evaluates actual store (i.code.lowered.expression.rename i.captured.embedding)
      (.inRight .word (value i.code i.captured.embedding history.native actual)) store ∧
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile).Represents
      registry mapping world (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native actual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (i.code.lowered.expression.rename i.captured.embedding) result finalStore →
      result = .inRight .word (value i.code i.captured.embedding history.native actual) ∧ finalStore = store) ∧
    CallableIndexedOwnedPreparedOrdinaryFormedMembers.FormedAt headers keys registry faults
      mapping world (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native actual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) ∧
    ChosenAt root expressionSyntax headers keys registry faults i history := by
  obtain ⟨sourceTrace, evaluated, related, determined, formed, factory⟩ :=
    CallableIndexedOwnedChosenOrdinaryFormedMembers.formation_member_with_factory root expressionSyntax
      receipt chosen environment captured prefixContext owner initial packet profile observed stored
  let i := CallableIndexedOwnedChosenOrdinaryFormedMembers.index receipt environment captured prefixContext
  let history := CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at i.captured i.code i.support owner initial packet
  have member : ChosenAt root expressionSyntax headers keys registry faults i history :=
    .ordinary owner factory
      (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.source_origin i.captured i.code i.support owner initial packet)
      rfl observed (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.reference_index i.captured i.code i.support)
      ((CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile).runtime_hasType
        (registry := registry) related)
  exact ⟨sourceTrace, evaluated, related, determined, formed, member⟩
end Formation

theorem written_chosen_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {heap after : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
    {target : Location} {cell : Dynamic.Cell}
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      i.mapping i.world heap store)
    (reference : ReferenceRepresents i.mapping i.world location target (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore))
    (read : Dynamic.Heap.Reads heap location cell) (cellType : cell.type = (FunctionValues.sourceType i.function))
    (member : ChosenAt root expressionSyntax headers keys registry faults i history)
    (written : Dynamic.Heap.Writes heap location (some (.closure i.function)) after) :
    ∃ updated, store.write? target (.inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)) = some updated ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
        i.mapping i.world after updated ∧
      AdministrativePreserved i.mapping store i.mapping updated ∧
      Dynamic.HeapMetadataExtend heap after ∧
      ChosenStoredAt root expressionSyntax headers keys registry faults i history after updated location := by
  obtain ⟨updated, writtenCore, finalHeaps, administrative, metadata, actualStored⟩ :=
    CallableIndexedOwnedPreparedOrdinaryStoredMembers.written_member profile heaps reference read cellType member.formed written
  exact ⟨updated, writtenCore, finalHeaps, administrative, metadata, member, actualStored.2⟩

open CallableIndexedHistory CallableIndexedAllocationCompletion

theorem allocated_chosen_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {layout : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (definitions : layouts.definitions = compiled.indexed.layouts.definitions)
    (frameRegistered : layout.Registered compiled.indexed.layouts.definitions)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {contextLocation : Location}
    {frame : NativeFrame} {sourceLocation : Dynamic.Location}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      i.mapping i.world administrative request.scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      i.mapping i.world before store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout frame))
    (payloadAt : PayloadAt request actual (some (value i.code i.captured.embedding history.native i.capturedActual)))
    (payloadType : request.payloadType = (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore))
    (member : ChosenAt root expressionSyntax headers keys registry faults i history)
    (allocated : Dynamic.Heap.Allocates before (FunctionValues.sourceType i.function) (some (.closure i.function)) sourceLocation after) :
    ∃ captured,
      Captures actual request.references request.scope captured ∧
      RuntimeValueHasType i.world captured (SourceCoreSourceCells.captureType request.scope) compiled.indexed.layouts.definitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
        (i.mapping ++ [store.length + 2])
        (i.world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) ∧
      ReferenceRepresents (i.mapping ++ [store.length + 2])
        (i.world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved i.mapping store (i.mapping ++ [store.length + 2])
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) ∧
      ChosenStoredAt root expressionSyntax headers keys registry faults
        (extendIndex i (futureMap := i.mapping ++ [store.length + 2])
          (futureWorld := i.world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
          ⟨_, rfl⟩ ⟨_, rfl⟩) history after
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) sourceLocation := by
  obtain ⟨captured, selected, typed, evaluated, finalHeaps, finalReference, administrative, actualStored⟩ :=
    CallableIndexedOwnedPreparedOrdinaryStoredMembers.allocated_member profile allocation annotation same definitions
      frameRegistered environments agrees heaps reference read payloadAt payloadType member.formed allocated
  exact ⟨captured, selected, typed, evaluated, finalHeaps, finalReference, administrative,
    ChosenAt.extend root expressionSyntax member ⟨_, rfl⟩ ⟨_, rfl⟩, actualStored.2⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredMembers
