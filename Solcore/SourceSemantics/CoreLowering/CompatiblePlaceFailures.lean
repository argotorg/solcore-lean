import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhs

/-! Whole emitted assignments short-circuit on key and RHS faults, retaining
all preceding source effects. The executions of children are obtained from the
universal expression IH; neither phase accepts a child evaluation as its
static compiler contract. Structural missing-default guards are separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceFailures
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

theorem keys {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (meaning : Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {sourceLocation : Dynamic.Location} {cell : Dynamic.Cell} {index : Nat} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (lookup : Dynamic.Environment.LooksUp environment place.root sourceLocation)
    (read : Dynamic.Heap.Reads before sourceLocation cell)
    (trace : Dynamic.SourceProjectionsFault program context evidence source environment before place.projections reason after)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨target, coreLookup, _⟩ := environments.lookup_visible lookup slot
  have layout : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by intro _ _ found; exact found
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩ :=
    DataPlaceKeyOrder.preserves_fault children meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees layout [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) trace
  refine ⟨token, finalStore, finalMap, finalWorld, .target (.projectionExpression lookup read trace), ?_,
    tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
  apply execute_key_failure prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType
    (binaryOperator (prepared.route.leafType = .integer) operator) false invalid token
    (.cellRef (OptionalCell.cellType prepared.route.rootType) target) (.var coreLookup)
  simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

/-- This composition consumes a semantic resolution result, produced by
CompatiblePlaceResolution.preserves, and the independent RHS fault. It derives
the actual RHS run and suppresses modifier, setter, write and continuation. -/
theorem rhs {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {sourceTarget : Dynamic.ResolvedPlace} {coreEnvironment : Environment} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap after : Dynamic.Heap}
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf sourceTarget
      coreEnvironment initialStore initialMap initialWorld before targetHeap)
    (meaning : Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    {administrativeContext : Core.Context} {environment : Dynamic.Environment}
    {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (coreType : lowered.type = prepared.route.leafType)
    (environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (resolved : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    {index : Nat} (reference : coreEnvironment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    {reason : Dynamic.SemanticFault}
    (failed : Dynamic.ExpressionFaults program context evidence source environment targetHeap id reason after)
    (operator : Syntax.ValueAssignOp) (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after ∧
      Evaluates coreEnvironment initialStore
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends initialMap finalMap ∧ WorldExtends initialWorld finalWorld ∧
      AdministrativePreserved initialMap initialStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, store, mapping, world, result⟩ :=
    CompatiblePlaceRhs.preserves resolution meaning generated found environments locals (.fault failed)
  cases represented : result.represented with
  | @fault _ token tokenRep =>
    refine ⟨token, store, mapping, world, .rhs resolved failed, ?_, tokenRep, result.heaps,
      resolution.maps.trans result.maps, resolution.worlds.trans result.worlds,
      resolution.frame.trans result.frame, resolution.metadata.trans result.metadata⟩
    apply SourceCoreCompatibleDataPlaces.execute_rhs_failure prepared (.var index) (SourceCoreCalls.packArguments codes)
      lowered.expression next outputType (binaryOperator (prepared.route.leafType = .integer) operator) false invalid token
      (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target) (packValues resolution.values)
      (.inRight .unit resolution.snapshot) (.var reference) resolution.keysEvaluated resolution.snapshotEvaluated
    simpa only [coreType, snapshotEnvironment, keysEnvironment, referenceEnvironment] using result.evaluated

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceFailures
