import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds
import Solcore.SourceSemantics.CoreLowering.BuiltinCallSource
import Solcore.SourceSemantics.CoreLowering.BuiltinCallProtocol

/-! The real builtin call exposes ordered arguments below its original
source or native execution size. Callee construction and contract dispatch
are pure prefixes; their semantic agreement supplies no size bound. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinCallBounds
open Core Frontend SourceInference CoreProof CompatibleExpressionPrimitives
open BuiltinCalls BuiltinCalls.Protocol RecursiveNamedCallBounds

inductive SourceTraceAt (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (arguments : List ExpressionId) (function : BuiltinFunctionId) (size : Nat) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | argumentsFault {child reason after}
      (failed : SourceExecutionSize.ExpressionsFault program child context evidence source environment before arguments reason after)
      (smaller : child < size) :
      SourceTraceAt program context evidence source environment before arguments function size (.fault reason) after
  | apply {child values middle outcome after}
      (argumentsEvaluated : SourceExecutionSize.ExpressionsEvaluate program child context evidence source environment before arguments values middle)
      (applied : FunctionCallBody.Outcome program context evidence [] middle (.builtin ⟨function⟩) values outcome after)
      (smaller : child < size) :
      SourceTraceAt program context evidence source environment before arguments function size outcome after

theorem source_inv {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id callee : ExpressionId}
    {node : ExpressionNode} {type : Ty} {arguments : List ExpressionId} {function : BuiltinFunctionId}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (metadata : Metadata checked source id node type)
    (form : node.form = .call callee arguments (.builtinFunction function)) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    SourceTraceAt program context evidence source environment before arguments function size outcome after := by
  cases trace with
  | value evaluated =>
    obtain ⟨child, raw, smaller⟩ := RecursiveNamedExpressionSourceBounds.evaluation_raw_sized unique
      (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | builtinCall _ argumentsEvaluated applied =>
      exact .apply argumentsEvaluated (.value applied.sound)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
  | fault failed =>
    obtain ⟨child, raw, smaller⟩ := RecursiveNamedExpressionSourceBounds.fault_raw_sized unique
      (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | builtinArguments _ argumentsFailed =>
      exact .argumentsFault argumentsFailed
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
    | builtinApply _ argumentsEvaluated failed =>
      exact .apply argumentsEvaluated (.fault failed.sound)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)

theorem contracted_arguments_sized {function : BuiltinFunctionId} {identity contract unknown : Word}
    {environment : Environment} {store finalStore : Store} {arguments : Expr} {result : Value} {size : Nat}
    (completed : EvaluationSize size environment store
      (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
        (contracted function identity contract) arguments) result finalStore) :
    ∃ child argumentValue argumentStore, child < size ∧
      EvaluationSize child (.unit :: contractedValue function identity contract environment :: environment) store
        ((arguments.weakenAt 0).weakenAt 0) argumentValue argumentStore := by
  obtain ⟨tailSize, tailSmaller, tail⟩ := completed.bind_success
    (contracted_evaluates function identity contract environment store)
  have stage := CallableContract.dispatch_evaluates [⟨contract, none, none⟩] .beforeArguments unknown contract
    (show Evaluates (contractedValue function identity contract environment :: environment) store
      (.second (.var 0)) (.word contract) store from .second (.var rfl))
  rw [gates_accept] at stage
  obtain ⟨nextSize, nextSmaller, next⟩ := tail.bind_success stage
  obtain ⟨child, argumentStore, argumentValue, smaller, evaluated⟩ := next.bind_computation
  exact ⟨child, argumentValue, argumentStore, Nat.lt_trans smaller (Nat.lt_trans nextSmaller tailSmaller), evaluated⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinCallBounds
