import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceBounds
import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceMeaning

/-! These consumers keep the original raw, operand, body and suffix witnesses.
In particular a synthetic two-operand fault list is not a strict child of the
original whole binary-right fault. This unit adds no runtime runner. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedOperatorSourceBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallablePreparedOperatorSourceBounds CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableCoercionExpressionCertificates (Projector Specialized Lowered)

abbrev legacy_raw := @CallablePreparedOperatorSourceMeaning.OperatorSource.raw_inv
abbrev legacy_whole := @CallablePreparedOperatorSourceMeaning.OperatorSource.source_inv

section OriginalChildren
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence invocation : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
  {left right : ExpressionId} {leftSize rightSize : Nat} {value : Dynamic.Value}
  {reason : Dynamic.SemanticFault}
  (leftEvaluated : SourceExecutionSize.ExpressionEvaluates program leftSize context evidence source environment
    before left value middle)
  (rightFailed : SourceExecutionSize.ExpressionFaults program rightSize context evidence source environment
    middle right reason after)

include leftEvaluated rightFailed in
/-- Both operands retain strict bounds under the original raw parent. -/
theorem right_fault_original_children :
    ArgumentsFaultAt program (SourceExecutionSize.stepSize [leftSize, rightSize]) context evidence source environment
      before [left, right] reason after :=
  .tail leftEvaluated (SourceExecutionSize.child_lt_stepSize (by simp))
    (.head rightFailed (SourceExecutionSize.child_lt_stepSize (by simp)))

include leftEvaluated rightFailed in
/-- The synthetic list adds a constructor. Its grade equals the whole form
fault, so claiming a strict bound for that list would be incorrect. -/
theorem synthetic_right_fault :
    SourceExecutionSize.ExpressionsFault program
      (SourceExecutionSize.stepSize [leftSize, SourceExecutionSize.stepSize [rightSize]])
      context evidence source environment before [left, right] reason after :=
  .tail leftEvaluated (.head rightFailed)

theorem synthetic_fault_grade (leftSize rightSize : Nat) :
    SourceExecutionSize.stepSize [leftSize, SourceExecutionSize.stepSize [rightSize]] =
      SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [leftSize, rightSize]] ∧
    ¬ SourceExecutionSize.stepSize [leftSize, SourceExecutionSize.stepSize [rightSize]] <
      SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [leftSize, rightSize]] := by
  simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]
  omega

include leftEvaluated rightFailed in
theorem repeated_occurrence (same : right = left) :
    ArgumentsFaultAt program (SourceExecutionSize.stepSize [leftSize, rightSize]) context evidence source environment
      before [left, left] reason after := by
  simpa only [same] using right_fault_original_children leftEvaluated rightFailed

variable {budget bodySize : Nat} {body : Dynamic.BodyInstance} {ids : List ExpressionId}
  {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}

include leftEvaluated rightFailed in
/-- The view comes from exactly the original binary-right constructor; the
right fault leaves the method body uninvoked. -/
theorem right_fault_form (operator : Syntax.BinaryOp) (requirements : List RequirementId)
    (coercions : List CoercionStep) (owned : List RequirementId)
    (layout : Dynamic.OrdinaryRequirementLayout requirements coercions owned)
    (evaluateRight : Dynamic.EvaluatesRightOperand operator value) :
    SourceExecutionSize.ExpressionFormFaults program (SourceExecutionSize.stepSize [leftSize, rightSize])
      context evidence source environment before (.binary left operator right) requirements coercions reason after ∧
    RawTraceAt program (SourceExecutionSize.stepSize [leftSize, rightSize]) context evidence invocation source environment
      before [left, right] body (.fault reason) after :=
  ⟨.binaryRight layout leftEvaluated evaluateRight rightFailed,
    .argumentFault (right_fault_original_children leftEvaluated rightFailed)⟩

/-- The original body witness and source dictionary remain available without
rerunning the source or choosing a new grade. -/
theorem actual_body_child
    (operands : ArgumentsAt program budget context evidence source environment before ids arguments middle)
    (called : RecursiveNamedCallBounds.BodyOutcome program bodySize body invocation middle arguments outcome after)
    (strict : bodySize < budget) :
    RawTraceAt program budget context evidence invocation source environment before ids body outcome after :=
  .apply operands called strict

theorem full_dictionary_and_heap
    (trace : RawTraceAt program budget context evidence invocation source environment before ids body outcome after) :
    NamedCalls.Arguments.Trace program context evidence invocation source environment before ids body outcome after :=
  trace.sound

end OriginalChildren

section Whole
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
  {outcome : Dynamic.ExpressionOutcome} {size : Nat}

/-- The original suffix size and its input heap are returned separately. -/
theorem whole_children
    (found : source.lookupExpression? id = some node) (unique : NodeOccurrencesUnique source)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder))
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    TraceForAt (fun child => RawOutcomeAt program child context evidence source environment before node)
      (fun child heap value => PathAt program child context evidence heap node.coercions value) size outcome after :=
  raw_source_inv_sized found unique notLocal trace

end Whole

section ActualSelected
variable {checkedProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  {receipt : Operator checkedProgram project caller compilation child fuel source scope id reasonAt policy node output}
  (selected : OperatorSource receipt)
  {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence dictionary : Dynamic.EvidenceEnvironment}
  {sourceBody : Dynamic.BodyInstance}
  (catalog : CallableCoercionSelectionIdentity.Catalog program)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)
  (selection : Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
    receipt.requirements sourceBody dictionary)

include selected catalog ledger selection in
theorem actual_raw {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (raw : RawOutcomeAt program size context evidence source environment before node outcome after) :
    ∃ actualDictionary,
      Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
        receipt.requirements sourceBody actualDictionary ∧
      RawTraceAt program size context evidence actualDictionary source environment before
        receipt.arguments sourceBody outcome after :=
  CallablePreparedOperatorSourceBounds.OperatorSource.raw_inv_sized selected catalog ledger selection raw

include selected catalog ledger selection in
theorem actual_whole {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (unique : NodeOccurrencesUnique source)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    TraceForAt
      (fun rawSize rawOutcome rawHeap => ∃ actualDictionary,
        Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
          receipt.requirements sourceBody actualDictionary ∧
        RawTraceAt program rawSize context evidence actualDictionary source environment before
          receipt.arguments sourceBody rawOutcome rawHeap)
      (fun pathSize heap value => PathAt program pathSize context evidence heap node.coercions value)
      size outcome after :=
  CallablePreparedOperatorSourceBounds.OperatorSource.source_inv_sized selected catalog ledger selection unique trace

end ActualSelected

end Tests.SourceCoreCallablePreparedOperatorSourceBounds
