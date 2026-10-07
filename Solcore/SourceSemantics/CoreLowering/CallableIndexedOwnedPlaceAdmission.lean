import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence
import Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder

/-! Genuine Source place typing supplies exactly the ordered key occurrences.
The actual resolution trace establishes deep heap typing at the same reached
getter state; stable rows use only its real administrative preservation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPlaceAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

/-- Members contribute no key expression. Every index retains its original
position, including duplicate expression occurrences. -/
theorem projections_keys_typed {source : TypedSource} {context : SourceSemantics.Context}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    (typing : SourceProjectionsHaveType source context root projections leaf) :
    ∃ originalSourceTypes,
      ExpressionsHaveTypes source context (DataPlaceKeyOrder.sourceKeys projections) originalSourceTypes := by
  cases projections with
  | nil =>
    cases typing
    exact ⟨[], .nil _⟩
  | cons projection rest =>
    cases projection with
    | member name index =>
      cases typing with
      | member _ restTyped => exact projections_keys_typed (projections := rest) restTyped
    | index key =>
      cases typing with
      | index keyTyped restTyped =>
        obtain ⟨types, typed⟩ := projections_keys_typed (projections := rest) restTyped
        exact ⟨_ :: types, .cons keyTyped typed⟩
termination_by projections.length

/-- A genuinely typed target supplies the same ordered key row without a
native type-vector equality. -/
theorem place_keys_typed {source : TypedSource} {context : SourceSemantics.Context}
    {place : PlaceResolution} {type : TypeSystem.Ty}
    (typing : SourcePlaceHasType source context place type) :
    ∃ originalSourceTypes,
      ExpressionsHaveTypes source context (DataPlaceKeyOrder.sourceKeys place.projections) originalSourceTypes := by
  cases typing with
  | intro _ projections _ => exact projections_keys_typed projections

/-- Both Source assignment forms retain their genuine raw target type. -/
theorem assignment_target_typed {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (typing : SourceAssignmentHasType source context assignment operator rhs) :
    ∃ type, SourcePlaceHasType source context assignment.target type := by
  cases typing <;> exact ⟨_, by assumption⟩

/-- Normalize only an actual ordered key member to its retained Source node.
The original typing row and unique occurrence lookup justify the equality. -/
theorem key_expression_typed {source : TypedSource} {context : SourceSemantics.Context}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    {id : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (typing : SourceProjectionsHaveType source context root projections leaf)
    (member : id ∈ DataPlaceKeyOrder.sourceKeys projections)
    (found : source.lookupExpression? id = some node) :
    ExpressionHasType source context id node.type := by
  obtain ⟨types, original⟩ := projections_keys_typed typing
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique original member found

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)

/-- Resolution's actual Source endpoint is also the getter state's Source
heap. The getter's real cumulative frame retains every reached row's history. -/
theorem after_resolution {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {place : PlaceResolution}
    {target : Dynamic.ResolvedPlace} {type : TypeSystem.Ty}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : SourcePlaceHasType source context place type)
    (trace : Dynamic.SourcePlaceResolves program context evidence source environment
      initial.heap place target reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    Admission bridge context last := by
  have expressionPreserves : Dynamic.ExpressionExecutionPreserves program context evidence source environment := by
    intro before after id value type covers locals heapTyped typed evaluated
    exact wellFormed.wholeLanguagePreservation.expression context evidence source environment
      before after id value type runtime covers locals heapTyped typed evaluated
  obtain ⟨rootType, _resolved, heapTyped, _extension⟩ :=
    trace.preserves expressionPreserves covers locals admitted.heap typed
  exact ⟨heapTyped,
    StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame⟩

/-- Keep the independent original Source resolution grade and the same actual
reached getter state. -/
theorem after_resolution_sized {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {place : PlaceResolution}
    {target : Dynamic.ResolvedPlace} {type : TypeSystem.Ty} {size : Nat}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : SourcePlaceHasType source context place type)
    (trace : SourceExecutionSize.SourcePlaceResolves program size context evidence source environment
      initial.heap place target reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    Admission bridge context last :=
  after_resolution bridge context first last admitted wellFormed runtime covers locals typed trace.sound frame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPlaceAdmission
