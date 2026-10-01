import Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentReflection

/-! A universal expression IH consumes the real seven-slot continuation output
of assignment reflection. The resulting trace preserves assignment-prefix
faults and effects before a successful or faulting continuation expression. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceContinuationReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces

/-- Independent source sequencing, expressed using the existing assignment and
expression relations. This adds no evaluator or runtime-value assumption. -/
inductive Trace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (place : PlaceResolution) (operator : Syntax.ValueAssignOp)
    (rhs next : ExpressionId) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | fault {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
      (assignment : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after) :
      Trace program context evidence source environment before place operator rhs next (.fault reason) after
  | sequence {updated : Dynamic.Value} {written after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
      (assignment : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated written)
      (continuation : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment written next outcome after) :
      Trace program context evidence source environment before place operator rhs next outcome after

/-- The assignment argument is the already proved semantic output of whole
execute reflection. The continuation's actual Core trace is extracted from it
and supplied to the universal child theorem under the exact hidden slots. -/
theorem reflects {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
    (meaning : Reflects (payloadModel checked.catalog signatures functions) program context evidence source certificate faults)
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    {place : PlaceResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {result : Value}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (assignment : DataPlaceTailReflection.Result checked signatures functions program context evidence source faults
      place operator rhs environment coreEnvironment before store mapping world lowered.expression lowered.type result finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program context evidence source environment before place operator rhs id outcome after ∧
      ResultRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld node.type lowered.type faults outcome result ∧
      GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases assignment with
  | fault trace resultEq tokenRep heaps maps worlds frame metadata =>
    subst result
    exact ⟨_, _, _, _, .fault trace, .fault tokenRep, heaps, maps, worlds, frame, metadata⟩
  | @committed updated writtenHeap written prefixMap prefixWorld slots trace heaps maps worlds frame metadata length continuation =>
    have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
      intro index value found; exact found
    obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata⟩ :=
      DataPlaceChildExpressions.reflects meaning generated found (environments.extend maps worlds) heaps
        (locals.mono metadata) sameEnvironment slots (by simpa only [length, Expr.rename_id] using continuation)
    exact ⟨outcome, after, finalMap, finalWorld, .sequence trace sourceTrace, related, finalHeaps,
      maps.trans finalMaps, worlds.trans finalWorlds, frame.trans finalFrame, metadata.trans finalMetadata⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceContinuationReflection
