import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryFormedMembers
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOrdinaryAllocation

/-! A known formed member stays beside its literal initialized Source cell and
native optional payload. Heap representation alone does not recover this
qualification, and mutation transport requires the actual future reads. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryStoredMembers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedOrdinaryFormedMembers
open CallableIndexedOwnedFunctionValues (Header Key)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {raw : TypeSystem.Ty}
  {source : Dynamic.Value} {native : Value} {type : Ty}

/-- The actual initialized payload and its known formed constructor. The
location and native target are exposed only within proof goals. -/
def StoredAt (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (location : Dynamic.Location) (raw : TypeSystem.Ty) (source : Dynamic.Value)
    (native : Value) (type : Ty) : Prop :=
  FormedAt headers keys registry faults mapping world raw source native type ∧
  ∃ target, ReferenceRepresents mapping world location target type ∧
    Dynamic.Heap.Reads heap location ⟨raw, some source, none⟩ ∧
    store.read? target = some (.inRight .unit native)

/-- Inject the retained function constructor into the unchanged payload model. -/
theorem payload_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (member : FormedAt headers keys registry faults mapping world raw source native type) :
    ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      mapping world raw source native type := by
  cases member with
  | ordinary i owner history origin prefixContext globals referenceIndex typed =>
    exact .function (.prepared_ordinary owner i.captured i.code history i.support origin
      prefixContext globals referenceIndex typed i.prepared)

/-- Actual future reads are necessary when the heap or store may have changed. -/
theorem StoredAt.extend_with_reads {heap futureHeap : Dynamic.Heap} {store futureStore : Store}
    {location : Dynamic.Location} {futureMap : LocationMap} {futureWorld : StoreTyping}
    (stored : StoredAt headers keys registry faults mapping world heap store location raw source native type)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (reads : Dynamic.Heap.Reads futureHeap location ⟨raw, some source, none⟩)
    (nativeReads : ∀ target, ReferenceRepresents mapping world location target type →
      futureStore.read? target = some (.inRight .unit native)) :
    StoredAt headers keys registry faults futureMap futureWorld futureHeap futureStore location raw source native type := by
  obtain ⟨member, target, reference, _, _⟩ := stored
  exact ⟨member.extend maps worlds, target, reference.extend maps worlds, reads, nativeReads target reference⟩

/-- Key transport preserves the same owner/frame observation and stored value. -/
theorem StoredAt.map_keys {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
    {futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys)
    (stored : StoredAt headers keys registry faults mapping world heap store location raw source native type) :
    StoredAt headers futureKeys registry faults mapping world heap store location raw source native type := by
  exact ⟨stored.1.map_keys embedding, stored.2⟩

/-- One real initialized write retains the same formed payload. Its nominal
Source declaration type is supplied independently of native projection. -/
theorem written_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {heap after : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
    {target : Location} {cell : Dynamic.Cell}
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      mapping world heap store)
    (reference : ReferenceRepresents mapping world location target type)
    (read : Dynamic.Heap.Reads heap location cell) (cellType : cell.type = raw)
    (member : FormedAt headers keys registry faults mapping world raw source native type)
    (written : Dynamic.Heap.Writes heap location (some source) after) :
    ∃ updated, store.write? target (.inRight .unit native) = some updated ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
        mapping world after updated ∧
      AdministrativePreserved mapping store mapping updated ∧
      Dynamic.HeapMetadataExtend heap after ∧
      StoredAt headers keys registry faults mapping world after updated location raw source native type := by
  have represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      mapping world cell.type source native type := cellType.symm ▸ payload_member profile member
  obtain ⟨updated, coreWritten, finalHeaps, administrative⟩ :=
    GenericHeap.HeapRepresents.write_initialized heaps reference read represented written
  obtain ⟨old, oldValue, oldPayload, oldRead, _, _, oldRelated⟩ := heaps.cells reference.mapped
  have same := oldRead.functional read
  subst old
  have ordinary := oldRelated.ordinary
  obtain ⟨previous, previousRead, afterRead⟩ := written.reads_updated
  have same := previousRead.functional read
  subst previous
  have initialized : Dynamic.Heap.Reads after location ⟨raw, some source, none⟩ := by
    simpa only [cellType, ordinary] using afterRead
  exact ⟨updated, coreWritten, finalHeaps, administrative, .of_write written,
    member, target, reference, initialized, Store.write?_reads_written coreWritten⟩

open CallableIndexedHistory CallableIndexedAllocationCompletion

/-- The actual marked allocation runs once and retains its complete snapshot,
marker, capture, heap and frame receipts beside the new initialized member. -/
theorem allocated_member
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
      mapping world administrative request.scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      mapping world before store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout frame))
    (payloadAt : PayloadAt request actual (some native))
    (payloadType : request.payloadType = type)
    (member : FormedAt headers keys registry faults mapping world raw source native type)
    (allocated : Dynamic.Heap.Allocates before raw (some source) sourceLocation after) :
    ∃ captured,
      Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope) compiled.indexed.layouts.definitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit native]) ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
        (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit native]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved mapping store (mapping ++ [store.length + 2])
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit native]) ∧
      StoredAt headers keys registry faults (mapping ++ [store.length + 2])
        (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit native])
        sourceLocation raw source native type := by
  subst type
  have cell : GenericHeap.CellRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      mapping world ⟨raw, some source, none⟩ (optionalValue request.payloadType (some native)) request.payloadType :=
    .initialized (payload_member profile member)
  obtain ⟨captured, selected, typed, evaluated, finalHeaps, finalReference, administrative⟩ :=
    CallableIndexedOrdinaryAllocation.preserves_with_captures_for_type allocation annotation same definitions
      frameRegistered environments agrees heaps reference read payloadAt cell allocated
  have maps : LocationMap.Extends mapping (mapping ++ [store.length + 2]) := ⟨_, rfl⟩
  have worlds : WorldExtends world
      (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType]) := ⟨_, rfl⟩
  have stored : StoredAt headers keys registry faults (mapping ++ [store.length + 2])
      (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
      after (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit native])
      sourceLocation raw source native request.payloadType := by
    refine ⟨member.extend maps worlds, store.length + 2, finalReference, allocated.reads_new, ?_⟩
    simp [Store.read?]
  exact ⟨captured, selected, typed, evaluated, finalHeaps, finalReference, administrative, stored⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryStoredMembers
