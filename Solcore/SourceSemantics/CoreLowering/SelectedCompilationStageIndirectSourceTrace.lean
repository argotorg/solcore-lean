import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds

/-! Actual ordinary indirect evaluation exposes the callee before the ordered
arguments. Empty accepted argument coercions preserve the complete value list
at its original arity, without using a Source body preservation premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectSourceTrace
open Core Frontend SourceInference

inductive TraceAt (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (callee : ExpressionId) (arguments : List ExpressionId) (size : Nat) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | calleeFault {child reason after}
      (failed : SourceExecutionSize.ExpressionFaults program child context evidence source environment before callee reason after)
      (smaller : child < size) : TraceAt program context evidence source environment before callee arguments size (.fault reason) after
  | notCallable {child value after}
      (evaluated : SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before callee value after)
      (invalid : ¬ Dynamic.CallableValue value)
      (smaller : child < size) : TraceAt program context evidence source environment before callee arguments size (.fault .notCallable) after
  | argumentsFault {calleeSize argumentsSize value middle reason after}
      (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee value middle)
      (callable : Dynamic.CallableValue value)
      (failed : SourceExecutionSize.ExpressionsFault program argumentsSize context evidence source environment middle arguments reason after)
      (calleeSmaller : calleeSize < size) (argumentsSmaller : argumentsSize < size) :
      TraceAt program context evidence source environment before callee arguments size (.fault reason) after
  | apply {calleeSize argumentsSize callSize value middle values argumentHeap invocation outcome after}
      (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee value middle)
      (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment middle arguments values argumentHeap)
      (called : RecursiveNamedCallBounds.CallOutcome program callSize context evidence invocation argumentHeap value values outcome after)
      (calleeSmaller : calleeSize < size) (argumentsSmaller : argumentsSize < size) (callSmaller : callSize < size) :
      TraceAt program context evidence source environment before callee arguments size outcome after

private theorem values_length {program : Program} {size : Nat} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {ids : List ExpressionId} {values : List Dynamic.Value}
    (trace : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment before ids values after) :
    ids.length = values.length := by
  induction ids generalizing size before values with
  | nil => cases trace; rfl
  | cons id ids ih =>
    cases trace with
    | cons head tail => exact congrArg Nat.succ (ih tail)

theorem source_inv
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id callee : ExpressionId} {arguments : List ExpressionId} {resolution : IndirectCallResolution}
    {node : ExpressionNode} {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.indirect resolution))
    (coercions : node.coercions = []) (argumentCoercions : resolution.argumentCoercions = [])
    (arity : arguments.length = resolution.argumentCount)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    TraceAt program context evidence source environment before callee arguments size outcome after := by
  cases trace with
  | value evaluated =>
    obtain ⟨child, raw, smaller⟩ := RecursiveNamedExpressionSourceBounds.evaluation_raw_sized unique
      (lookupExpression?_sound found) (by intros; simp [form]) coercions evaluated
    rw [form] at raw
    cases raw with
    | indirectCall _ calleeTrace argumentsTrace packBefore path packAfter _sourceArity appliedArity applied =>
      rw [argumentCoercions] at path
      cases path
      have same := Dynamic.ValuesPack.injective_of_length_eq packBefore packAfter
        ((values_length argumentsTrace).symm.trans (arity.trans appliedArity.symm))
      cases same
      exact .apply calleeTrace argumentsTrace (.value applied)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
  | fault failed =>
    obtain ⟨child, raw, smaller⟩ := RecursiveNamedExpressionSourceBounds.fault_raw_sized unique
      (lookupExpression?_sound found) (by intros; simp [form]) coercions failed
    rw [form] at raw
    cases raw with
    | indirectCallee failed =>
      exact .calleeFault failed
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
    | indirectNotCallable evaluated invalid =>
      exact .notCallable evaluated invalid
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
    | indirectArguments calleeTrace callable failed =>
      exact .argumentsFault calleeTrace callable failed
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
    | indirectSourceArity _ _ mismatch => exact False.elim (mismatch arity.symm)
    | indirectArgumentCoercion _ _ _ _ failed => rw [argumentCoercions] at failed; cases failed
    | indirectApply calleeTrace argumentsTrace packBefore path packAfter _sourceArity appliedArity failed =>
      rw [argumentCoercions] at path
      cases path
      have same := Dynamic.ValuesPack.injective_of_length_eq packBefore packAfter
        ((values_length argumentsTrace).symm.trans (arity.trans appliedArity.symm))
      cases same
      exact .apply calleeTrace argumentsTrace (.fault failed)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)

/-- The actual named application fixes its complete invocation dictionary.
Pre-body faults retain their original reason and grade. -/
theorem call_with_global_evidence
    {program : Program} {context : SourceSemantics.Context}
    {caller invocation : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap}
    {function : Dynamic.GlobalFunction} {arguments : List Dynamic.Value}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.CallOutcome program size context caller invocation before
      (.global function) arguments outcome after) :
    RecursiveNamedCallBounds.CallOutcome program size context caller function.evidence before
      (.global function) arguments outcome after := by
  cases trace with
  | value applied =>
    cases applied with
    | global instantiated same covers body =>
      cases same
      exact .value (.global instantiated rfl covers body)
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | globalSignatureMissing missing => exact .fault (.globalSignatureMissing missing)
    | globalBodyMissing missing => exact .fault (.globalBodyMissing missing)
    | globalArity instantiated mismatch => exact .fault (.globalArity instantiated mismatch)
    | globalBody instantiated same body =>
      cases same
      exact .fault (.globalBody instantiated rfl body)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectSourceTrace
