import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceResolution
import Solcore.SourceSemantics.Dynamic.Initialization

/-! RHS execution uses the previously selected snapshot but returns the live
root in the post-RHS heap. Both directions instantiate the universal expression
IH under execute's real three hidden slots. None of the fields below is an
input to a compiler certificate; they are semantic output witnesses. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhs
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {sourceTarget : Dynamic.ResolvedPlace} {coreEnvironment : Environment} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap : Dynamic.Heap}

/-- The original reference is read against the actual post-RHS store.
The source cell's raw declared type survives; its value may have changed. -/
structure Latest (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    (prepared : Prepared) (sourceTarget : Dynamic.ResolvedPlace) (target : Location)
    (heap : Dynamic.Heap) (store : Store) where
  cell : Dynamic.Cell
  optional : Value
  read : Dynamic.Heap.Reads heap sourceTarget.location cell
  type : cell.type = prepared.route.rootSourceType
  reference : ReferenceRepresents mapping world sourceTarget.location target prepared.route.rootType
  nativeRead : store.read? target = some optional
  related : GenericHeap.CellRepresents (payloadModel checked registry functions) mapping world cell optional prepared.route.rootType

variable (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf sourceTarget
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
  heaps : HeapRepresents checked registry functions mapping world after store
  maps : LocationMap.Extends resolution.mapping mapping
  worlds : WorldExtends resolution.world world
  frame : AdministrativePreserved resolution.mapping resolution.store mapping store
  metadata : Dynamic.HeapMetadataExtend targetHeap after
  latest : Nonempty (Latest checked registry functions mapping world prepared sourceTarget resolution.target after store)

private theorem latest_of_heap {mapping : LocationMap} {world : StoreTyping} {after : Dynamic.Heap} {store : Store}
    (heaps : HeapRepresents checked registry functions mapping world after store)
    (maps : LocationMap.Extends resolution.mapping mapping) (worlds : WorldExtends resolution.world world)
    (metadata : Dynamic.HeapMetadataExtend targetHeap after) :
    Nonempty (Latest checked registry functions mapping world prepared sourceTarget resolution.target after store) := by
  obtain ⟨cell, read, sameType, _⟩ := metadata _ _ resolution.currentRead
  have reference := resolution.reference.extend maps worlds
  obtain ⟨optional, nativeRead, represented⟩ := CompatibleHeap.HeapRepresents.read_at heaps reference read
  exact ⟨⟨cell, optional, read, sameType.trans resolution.currentType, reference, nativeRead, represented⟩⟩

variable {administrativeContext : Core.Context} {environment : Dynamic.Environment}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}

/-- Every source RHS outcome executes under the actual saved snapshot slots.
The returned live-root receipt is derived from the IH's new heap. -/
theorem preserves
    (meaning : Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment targetHeap id outcome after) :
    ∃ value store mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment outcome after value store mapping world := by
  have layout : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by intro _ _ found; exact found
  obtain ⟨value, store, mapping, world, evaluated, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees layout
        [.inRight .unit resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) trace
  refine ⟨value, store, mapping, world, trace, ?_, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap resolution heaps maps worlds metadata⟩
  simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

/-- Completed RHS code reconstructs the independent source outcome and the
post-RHS live root, without supplying a source execution or child evaluation IH
at one preselected runtime environment. -/
theorem reflects
    (meaning : Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {value : Value} {store : Store}
    (evaluated : Evaluates
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values) (.inRight .unit resolution.snapshot) coreEnvironment)
      resolution.store (shift 3 lowered.expression) value store) :
    ∃ outcome after mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment outcome after value store mapping world := by
  have layout : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by intro _ _ found; exact found
  obtain ⟨outcome, after, mapping, world, trace, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees layout
        [.inRight .unit resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target])
      (by simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨outcome, after, mapping, world, trace, evaluated, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap resolution heaps maps worlds metadata⟩

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

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhs
