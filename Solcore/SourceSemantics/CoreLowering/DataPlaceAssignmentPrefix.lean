import Solcore.SourceSemantics.CoreLowering.DataPlaceResolvedTarget

/-! Whole emitted assignment faults before modification. The target keys and
snapshot getter are reconstructed from independent source resolution, and the
RHS is obtained from the universal child theorem under the real three slots.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentPrefix
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces DataPlaceExecution

theorem rhs_fault {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : DataPlaceResolvedTarget.Layout checked signatures functions source certificate scope place prepared codes sourceTypes
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
    (meaning : Preserves (payloadModel checked.catalog signatures functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : DataEquality.IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before targetHeap after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootType : sourceTarget.rootType = prepared.route.rootSourceType)
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    {reason : Dynamic.SemanticFault}
    (failed : Dynamic.ExpressionFaults program context evidence source environment targetHeap rhs reason after)
    (operator : Syntax.ValueAssignOp) (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧
      GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨target, coreLookup⟩ := DataPlaceResolvedTarget.preserves layout meaning observations faithful layouts
    environments heaps locals slot rootType resolve
  have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
    intro i v selected; exact selected
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    DataPlaceChildExpressions.preserves meaning rhsGenerated found
      (environments.extend target.maps target.worlds) target.heaps (locals.mono target.metadata) sameEnvironment
      [target.snapshot, packValues target.values, .cellRef (OptionalCell.cellType prepared.route.rootType) target.target]
      (.fault failed)
  cases represented with
  | @fault _ token reasonRep =>
    have rhsEvaluated : Evaluates
        (snapshotEnvironment prepared.route.rootType target.target (packValues target.values) target.snapshot coreEnvironment)
        target.store (shift 3 lowered.expression) (.inLeft lowered.type (.word token)) finalStore := by
      simpa only [Expr.rename_id, List.length_cons, List.length_nil, List.cons_append, List.nil_append,
        snapshotEnvironment, keysEnvironment, referenceEnvironment] using evaluated
    exact ⟨token, finalStore, finalMap, finalWorld, .rhs resolve failed,
      execute_rhs_failure (.var coreLookup) target.keysEvaluated target.snapshotEvaluated rhsEvaluated,
      reasonRep, finalHeaps, target.maps.trans maps, target.worlds.trans worlds,
      target.frame.trans frame, target.metadata.trans metadata⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentPrefix
