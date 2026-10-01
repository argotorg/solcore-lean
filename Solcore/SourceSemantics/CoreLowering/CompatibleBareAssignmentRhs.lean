import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentSnapshot
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhsReflection

/-! Typed RHS transport for a bare assignment uses its real renamed reference,
saved optional snapshot, and arbitrary administrative captures. Semantic phase
receipts below are outputs of the child induction, not static assumptions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}
  {faults : FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}

variable (snapshot : Snapshot checked registry functions prepared place environment actual heap store mapping world (ξ index))

structure RhsResult (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop where
  trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after
  evaluated : Evaluates (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
    store (shift 3 (lowered.expression.rename ξ)) value finalStore
  represented : ResultRepresents (payloadModel checked registry functions) finalMap finalWorld node.type lowered.type faults outcome value
  heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore
  maps : LocationMap.Extends mapping finalMap
  worlds : WorldExtends world finalWorld
  frame : AdministrativePreserved mapping store finalMap finalStore
  metadata : Dynamic.HeapMetadataExtend heap after
  latest : Nonempty (CompatiblePlaceRhs.Latest checked registry functions finalMap finalWorld prepared snapshot.resolved snapshot.target after finalStore)

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
  {certificate : Certificate}

theorem rhs_preserves
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
        (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) trace
  refine ⟨value, finalStore, finalMap, finalWorld, trace, ?_, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap snapshot heaps maps worlds metadata⟩
  simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

theorem rhs_reflects
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
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
      (snapshot.runtimeTyped actualTyped)
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace, evaluated, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap snapshot heaps maps worlds metadata⟩

/-- Strip only the actually executed reference, empty key tuple and getter.
The remaining computation evaluates the renamed RHS once. -/
theorem snapshot_prefix {compilation : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
    (layout : Layout compilation prepared)
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world (ξ index))
    (rhs next : Expr) (outputType : Ty) (operator : Option BinaryOp) (invalid : Word) :
    CoreProof.ContinuationAgreement actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) rhs next outputType operator false invalid).rename ξ)
      (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual) store
      (LanguageResult.bind outputType (shift 3 (rhs.rename ξ))
        (CompatiblePlaceRhsReflection.remainder prepared .unit (next.rename ξ) outputType operator invalid)) := by
  rw [execute_rename layout]
  exact (CoreProof.ContinuationAgreement.letE (.var snapshot.nativeLookup)).trans
    ((CoreProof.ContinuationAgreement.bind (keys_evaluates _ store)).trans
      (CoreProof.ContinuationAgreement.bind (snapshot.getter layout)))

end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
