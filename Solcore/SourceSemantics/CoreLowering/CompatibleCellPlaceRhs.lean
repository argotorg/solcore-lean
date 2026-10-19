import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhs
import Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceResolution
import Solcore.SourceSemantics.Dynamic.Initialization

/-! RHS execution uses the previously selected snapshot but returns the live
root in the post-RHS heap. Both directions instantiate the universal expression
IH under execute's real three hidden slots. None of the fields below is an
input to a compiler certificate; they are semantic output witnesses. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRhs
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlaceRhs (Latest)

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {sourceTarget : Dynamic.ResolvedPlace} {coreEnvironment : Environment} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap : Dynamic.Heap}

variable {cells : GenericHeap.CellModel ambient.definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}

variable (resolution : CompatibleCellPlaceResolution.Execution checked registry functions cells instances prepared codes sourceTypes place leaf sourceTarget
  coreEnvironment initialStore initialMap initialWorld before targetHeap)

/-- Snapshot, keys, and RHS all retain their own source/native identities.
The latest-root receipt refers to the new heap, not the saved snapshot heap. -/
structure Result (id : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr)
    (environment : Dynamic.Environment) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (store : Store) (mapping : LocationMap) (world : StoreTyping) : Prop where
  trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment targetHeap id outcome after
  evaluated : Evaluates
    (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values) (.inRight .unit resolution.snapshot) coreEnvironment)
    resolution.store (shift 3 lowered.expression) value store
  represented : ResultRepresents (payloadModel checked registry functions) mapping world node.type lowered.type faults outcome value
  heaps : GenericHeap.CellHeapRepresents cells mapping world after store
  maps : LocationMap.Extends resolution.mapping mapping
  worlds : WorldExtends resolution.world world
  frame : AdministrativePreserved resolution.mapping resolution.store mapping store
  metadata : Dynamic.HeapMetadataExtend targetHeap after
  effect : CellAwareScopeAuthority.Effect instances resolution.mapping resolution.world targetHeap resolution.store mapping world after store
  latest : Nonempty (Latest checked registry functions mapping world prepared sourceTarget resolution.target after store)

theorem latest_of_heap
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel checked registry functions) cells) {mapping : LocationMap} {world : StoreTyping} {after : Dynamic.Heap} {store : Store}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world after store)
    (maps : LocationMap.Extends resolution.mapping mapping) (worlds : WorldExtends resolution.world world)
    (metadata : Dynamic.HeapMetadataExtend targetHeap after) :
    Nonempty (Latest checked registry functions mapping world prepared sourceTarget resolution.target after store) := by
  obtain ⟨cell, read, sameType, sameDescriptor⟩ := metadata _ _ resolution.currentRead
  have reference := resolution.reference.extend maps worlds
  obtain ⟨optional, nativeRead, represented⟩ := CompatibleCellPlaceRoot.read_at ordinaryCells heaps reference read (sameDescriptor.trans resolution.ordinary)
  exact ⟨⟨cell, optional, read, sameType.trans resolution.currentType, reference, nativeRead, represented⟩⟩

variable {environment : Dynamic.Environment} {id : ExpressionId} {node : ExpressionNode}
  {lowered : SourceCoreBasic.LoweredExpr}

/-- RHS effects preserve the previous snapshot as a related value. It is not
replaced by the value obtained when the root is read again for writeback. -/
theorem Result.saved_snapshot {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    (result : Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment outcome after value store mapping world) :
    ValueRep checked registry functions mapping world leaf resolution.selected resolution.snapshot prepared.route.leafType :=
  resolution.snapshotRelated.extend (.refl _) result.maps result.worlds

/-- A successful source RHS cannot turn an initialized root into an absent
one. This fact comes from the independent trace, not the heap metadata law. -/
theorem Result.initialized {right : Dynamic.Value} {after : Dynamic.Heap}
    {value : Value} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    (result : Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment (.value right) after value store mapping world)
    (wasInitialized : resolution.currentCell.value ≠ none)
    (latest : Latest checked registry functions mapping world prepared sourceTarget resolution.target after store) :
    latest.cell.value ≠ none := by
  cases result.trace with
  | value trace =>
    obtain ⟨cell, read, initialized⟩ := trace.initialization_extends _ _ resolution.currentRead wasInitialized
    exact latest.read.functional read ▸ initialized

end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRhs
