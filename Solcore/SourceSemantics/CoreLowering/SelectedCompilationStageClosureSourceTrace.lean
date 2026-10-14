import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds

/-! The actual ordinary closure call supplies its full frame and allocation.
The retained mono parameter row identifies the original body context. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureSourceTrace
open Core Frontend SourceInference

private theorem binders_context_eq {owner : Resolved.DeclarationId}
    {before left right : SourceSemantics.Context} {parameters : List TypedBinder}
    {leftTypes rightTypes : List TypeSystem.Ty}
    (first : MonoBindersExtend owner before parameters leftTypes left)
    (second : MonoBindersExtend owner before parameters rightTypes right) : left = right := by
  have same := first.bodyTypes_eq.symm.trans second.bodyTypes_eq
  subst rightTypes
  exact first.functional second

theorem source_prefix {program : Program} {function : Dynamic.Closure}
    {callContext bodyContext : SourceSemantics.Context} {caller invocation : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {types : List TypeSystem.Ty}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters types bodyContext)
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext caller invocation before
      (.closure function) arguments outcome after) :
    ∃ childSize environment bound,
      Dynamic.ClosureFrame program function ∧
      Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace program childSize function bodyContext environment bound outcome after ∧
      childSize < size := by
  cases trace with
  | value applied =>
    cases applied with
    | closure _ valid extended allocated body returned =>
      have same := binders_context_eq extended parameters
      subst same
      subst_vars
      exact ⟨_, _, _, valid, allocated, .returned body, SourceExecutionSize.child_lt_stepSize (by simp)⟩
    | closureUnit _ valid unit extended allocated body fellThrough =>
      have same := binders_context_eq extended parameters
      subst same
      obtain ⟨environment, rfl⟩ := fellThrough
      exact ⟨_, _, _, valid, allocated, .unit unit body, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | closureArity mismatch => exact False.elim (mismatch arity)
    | closureBody _ valid extended allocated body =>
      have same := binders_context_eq extended parameters
      subst same
      exact ⟨_, _, _, valid, allocated, .fault body, SourceExecutionSize.child_lt_stepSize (by simp)⟩
    | closureControlEscape _ valid extended allocated body escaped =>
      have same := binders_context_eq extended parameters
      subst same
      exact ⟨_, _, _, valid, allocated, .escaped body escaped, SourceExecutionSize.child_lt_stepSize (by simp)⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureSourceTrace
