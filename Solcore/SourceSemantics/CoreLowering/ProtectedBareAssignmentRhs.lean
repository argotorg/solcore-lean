import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentCommit
import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning

/-! Guarded RHS transport uses the actual three saved native values and their
typing. The canonical installed entry remains unchanged; only actual variable
indices are shifted. The original snapshot/latest/RHS receipts are reused. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatibleBareAssignment

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}
  {faults : FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}

variable (snapshot : Snapshot checked registry functions prepared place environment actual heap store mapping world (ξ index))

private theorem latest_of_heap {nextMap : LocationMap} {nextWorld : StoreTyping} {after : Dynamic.Heap} {finalStore : Store}
    (heaps : HeapRepresents checked registry functions nextMap nextWorld after finalStore)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Nonempty (CompatiblePlaceRhs.Latest checked registry functions nextMap nextWorld prepared snapshot.resolved snapshot.target after finalStore) := by
  obtain ⟨cell, read, sameType, _⟩ := metadata _ _ snapshot.read
  have reference := snapshot.reference.extend maps worlds
  obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference read
  exact ⟨⟨cell, optional, read, sameType.trans snapshot.type, reference, nativeRead, represented⟩⟩

variable {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate} {entry : ProtectedExpressionMeaning.Entry}

theorem rhs_preserves
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults entry)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world heap store canonical)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
        (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) installed trace
  refine ⟨value, finalStore, finalMap, finalWorld, trace, ?_, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap snapshot heaps maps worlds metadata⟩
  simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

theorem rhs_reflects
    (meaning : ProtectedExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults entry)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world heap store canonical)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      store (shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
        (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) installed
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace, evaluated, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap snapshot heaps maps worlds metadata⟩


end Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignment
