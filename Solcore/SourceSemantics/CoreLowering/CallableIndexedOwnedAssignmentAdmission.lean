import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission

/-! Genuine Source assignment typing and the actual successful write trace
establish admission at the same reached caller state. Faults retain actual
stable rows through administrative preservation without a deep heap claim. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

/-- Normalize the genuine raw RHS typing to its exact retained occurrence. -/
theorem rhs_typed {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {node : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? rhs = some node)
    (typed : SourceAssignmentHasType source context assignment operator rhs) :
    ExpressionHasType source context rhs node.type := by
  have original : ∃ type, ExpressionHasType source context rhs type := by
    cases typed <;> exact ⟨_, by assumption⟩
  obtain ⟨type, original⟩ := original
  obtain ⟨actual, contains, sameType⟩ := original.stored_type
  have sameNode : actual = node := Option.some.inj
    ((lookupExpression?_complete unique contains).symm.trans found)
  subst actual
  exact sameType.symm ▸ original

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)

/-- The authentic successful Source assignment proves deep heap typing.
All stable histories belong to the actual reached pool. -/
theorem after_assignment {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {updated : Dynamic.Value}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : SourceAssignmentHasType source context assignment operator rhs)
    (trace : Dynamic.SourcePlaceAssignment program context evidence source
      (Dynamic.AssignmentValueApplies operator) environment initial.heap assignment.target rhs updated reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    Admission bridge context last := by
  have expressionPreserves : Dynamic.ExpressionExecutionPreserves program context evidence source environment := by
    intro before after id value type covers locals heapTyped typed evaluated
    exact wellFormed.wholeLanguagePreservation.expression context evidence source environment
      before after id value type runtime covers locals heapTyped typed evaluated
  have preserved := trace.preserves expressionPreserves covers locals admitted.heap typed
  exact ⟨preserved.1,
    StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame⟩

/-- Keep the original Source grade and actual completed written-prefix state. -/
theorem after_assignment_sized {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {updated : Dynamic.Value} {size : Nat}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : SourceAssignmentHasType source context assignment operator rhs)
    (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source
      (Dynamic.AssignmentValueApplies operator) environment initial.heap assignment.target rhs updated reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    Admission bridge context last :=
  after_assignment bridge context first last admitted wellFormed runtime covers locals typed trace.sound frame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentAdmission
