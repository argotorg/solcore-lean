import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForLiftBounds

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsSourceInversion
open Frontend SourceInference
open SelectedCompilationStageForLiftBounds

variable {program : Program} {invocation : Staging.Recursive.Scope}
  {context nextContext finalContext : SourceSemantics.Context}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {items : List ForItemForm} {binder : TypedBinder} {expression : ExpressionId}
  {size : Nat} {outcome : Dynamic.ControlOutcome}

theorem nil (trace : PlainItems program size invocation context environment before [] finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ after = before := by
  cases trace with
  | done trace => cases trace; exact ⟨rfl, rfl, rfl⟩
  | fault trace => cases trace

theorem absent (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : PlainItems program size invocation context environment before
      (.letDecl binder none :: items) finalContext outcome after) :
    ∃ tailSize location bound, tailSize < size ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location bound ∧
      PlainItems program tailSize invocation nextContext ((binder.id, location) :: environment)
        bound items finalContext outcome after := by
  cases trace with
  | done trace =>
    cases trace with
    | cons head tail =>
      cases head with
      | letUninitialized _ extension allocated =>
        cases Dynamic.BinderExtends.functional extended extension
        exact ⟨_, _, _, SourceExecutionSize.child_lt_stepSize (by simp), allocated, .done tail⟩
  | fault trace =>
    cases trace with
    | head failed => cases failed; contradiction
    | tail head failed =>
      cases head with
      | letUninitialized _ extension allocated =>
        cases Dynamic.BinderExtends.functional extended extension
        exact ⟨_, _, _, SourceExecutionSize.child_lt_stepSize (by simp), allocated, .fault failed⟩

theorem initialized (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : PlainItems program size invocation context environment before
      (.letDecl binder (some expression) :: items) finalContext outcome after) :
    (∃ child reason, child < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.fault reason) after) ∨
    (∃ child tailSize value middle location bound, child < size ∧ tailSize < size ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.value value) middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location bound ∧
      PlainItems program tailSize invocation nextContext ((binder.id, location) :: environment)
        bound items finalContext outcome after) := by
  cases trace with
  | done trace =>
    cases trace with
    | cons head tail =>
      cases head with
      | letInitialized evaluated _ extension allocated =>
        cases Dynamic.BinderExtends.functional extended extension
        refine .inr ⟨_, _, _, _, _, _, ?_, SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, allocated, .done tail⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
      | letInitializedGeneralized _ poly => exact (poly mono).elim
  | fault trace =>
    cases trace with
    | head failed =>
      cases failed with
      | polymorphicLet poly => exact (poly mono).elim
      | letInitializer _ failed =>
        refine .inl ⟨_, _, ?_, rfl, rfl, .fault failed⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
    | tail head failed =>
      cases head with
      | letInitialized evaluated _ extension allocated =>
        cases Dynamic.BinderExtends.functional extended extension
        refine .inr ⟨_, _, _, _, _, _, ?_, SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, allocated, .fault failed⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
      | letInitializedGeneralized _ poly => exact (poly mono).elim

theorem discard (trace : PlainItems program size invocation context environment before
      (.expression expression :: items) finalContext outcome after) :
    (∃ child reason, child < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.fault reason) after) ∨
    (∃ child tailSize value middle, child < size ∧ tailSize < size ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.value value) middle ∧
      PlainItems program tailSize invocation context environment middle items finalContext outcome after) := by
  cases trace with
  | done trace =>
    cases trace with
    | cons head tail =>
      cases head with
      | expression evaluated =>
        refine .inr ⟨_, _, _, _, ?_, SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, .done tail⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
  | fault trace =>
    cases trace with
    | head failed =>
      cases failed with
      | expression failed =>
        refine .inl ⟨_, _, ?_, rfl, rfl, .fault failed⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
    | tail head failed =>
      cases head with
      | expression evaluated =>
        refine .inr ⟨_, _, _, _, ?_, SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, .fault failed⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsSourceInversion
