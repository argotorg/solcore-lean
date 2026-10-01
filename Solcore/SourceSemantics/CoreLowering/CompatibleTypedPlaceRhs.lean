import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhs
import Solcore.SourceSemantics.CoreLowering.TypedGenericExpressionMeaning

/-! The saved snapshot, packed keys and captured root reference are the actual
three RHS slots. Their typing is derived from resolution receipts and the
canonical lexical environment, rather than supplied as a child execution.
The result and latest-root relations are shared with unrestricted RHS meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceRhs
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceRhs

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {sourceTarget : Dynamic.ResolvedPlace} {coreEnvironment : Environment} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap : Dynamic.Heap}

variable (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf sourceTarget
  coreEnvironment initialStore initialMap initialWorld before targetHeap)

/-- Every hidden slot uses the post-getter world. Existing administrative
captures are transported by the exact world extension from resolution. -/
theorem snapshot_runtimeTyped {administrativeContext : Core.Context} {environment : Dynamic.Environment}
    {scope : Scope}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      initialMap initialWorld administrativeContext scope environment coreEnvironment) :
    RuntimeEnvironmentHasTypes resolution.world
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) coreEnvironment)
      (OptionalCell.cellType prepared.route.leafType :: (SourceCoreCalls.packArguments codes).type ::
        OptionalCell.referenceType prepared.route.rootType ::
        (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) ambient.definitions :=
  .cons (.inRight resolution.snapshotRelated.runtime_hasType)
    (.cons (CompatiblePlaceResolution.values_typed resolution.keysRelated)
      (.cons (.cellRef resolution.reference.typed)
        (environments.extend resolution.maps resolution.worlds).runtime_hasTypes))

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
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment targetHeap id outcome after) :
    ∃ value store mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment outcome after value store mapping world := by
  have layout : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by intro _ _ found; exact found
  have actualTyped := snapshot_runtimeTyped resolution environments
  obtain ⟨value, store, mapping, world, evaluated, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees layout
        [.inRight .unit resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) actualTyped trace
  refine ⟨value, store, mapping, world, trace, ?_, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap resolution heaps maps worlds metadata⟩
  simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

/-- Completed RHS code reconstructs the independent source outcome and the
post-RHS live root, without supplying a source execution or child evaluation IH
at one preselected runtime environment. -/
theorem reflects
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
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
  have actualTyped := snapshot_runtimeTyped resolution environments
  obtain ⟨outcome, after, mapping, world, trace, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees layout
        [.inRight .unit resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) actualTyped
      (by simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨outcome, after, mapping, world, trace, evaluated, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap resolution heaps maps worlds metadata⟩


end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceRhs
