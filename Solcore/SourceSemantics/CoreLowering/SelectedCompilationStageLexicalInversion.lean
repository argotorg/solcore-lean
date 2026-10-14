import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedLiftBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds

variable {program : Program} {source : TypedSource}
  {context nextContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {binder : TypedBinder}
  {size : Nat} {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

private theorem selected (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {other}
    (contains : ContainsStatement source id other) : other = node :=
  Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)

theorem absent_value (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
    (extended : BinderExtends source.owner context binder nextContext)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment
      before id finalContext outcome after) :
    size = SourceExecutionSize.stepSize [] ∧ finalContext = nextContext ∧
      ∃ location, outcome = .fallthrough ((binder.id, location) :: environment) ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location after := by
  cases trace <;> have same := selected unique found (by assumption) <;> subst_vars <;> simp_all
  rename_i extension allocated
  have equal := Dynamic.BinderExtends.functional extended extension
  exact equal.symm

theorem absent_fault (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
    (mono : binder.scheme.quantified = [])
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment
      before id reason after) : False := by
  cases trace
  case missing absent => exact Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  all_goals have same := selected unique found (by assumption)
  all_goals subst_vars
  all_goals simp_all

 theorem initialized_value {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some expression))
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment
      before id finalContext outcome after) :
    ∃ child value middle location, size = SourceExecutionSize.stepSize [child] ∧ finalContext = nextContext ∧
      outcome = .fallthrough ((binder.id, location) :: environment) ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment
        before expression value middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location after := by
  cases trace <;> have same := selected unique found (by assumption) <;> subst_vars <;> simp_all
  rename_i _contains extension allocated
  have equal := Dynamic.BinderExtends.functional extended extension
  exact ⟨_, rfl, equal.symm, _, _, by assumption, allocated⟩

theorem initialized_fault {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some expression))
    (mono : binder.scheme.quantified = [])
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment
      before id reason after) :
    ∃ child, child < size ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment
        before expression reason after := by
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := selected unique found (by assumption)
  all_goals subst_vars
  all_goals simp_all
  refine ⟨_, ?_, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)


private theorem empty_trace {mode : Bool} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap} :
    PlainStatements program mode (SourceExecutionSize.stepSize []) invocation context environment heap
      [] context (.fallthrough environment) heap := by
  cases mode <;> exact .control .nil

/-- The accepted absent declaration performs its exact ordinary allocation
and continues in the extended lexical context. -/
theorem absent {mode : Bool} {invocation : Staging.Recursive.Scope} {rest : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ tailSize location bound, tailSize < size ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location bound ∧
      PlainStatements program mode tailSize invocation nextContext ((binder.id, location) :: environment)
        bound rest finalContext outcome after := by
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨_, _, _, _, _, failed⟩ | ⟨_, strict, stopped, head⟩ |
    ⟨_, tailSize, middleContext, nextEnvironment, middle, _, tailStrict, head, tail⟩
  · exact (absent_fault unique found form mono failed).elim
  · obtain ⟨rfl, equalContext, location, equalOutcome, allocated⟩ := absent_value unique found form extended head
    subst finalContext
    subst outcome
    rcases stopped with impossible | rfl
    · cases impossible
    · exact ⟨SourceExecutionSize.stepSize [], location, after, strict, allocated, empty_trace⟩
  · obtain ⟨_, equalContext, location, equalOutcome, allocated⟩ := absent_value unique found form extended head
    subst middleContext
    cases equalOutcome
    exact ⟨tailSize, location, middle, tailStrict, allocated, tail⟩

/-- An initializer fault precedes allocation. Successful initialization keeps
both its exact expression heap and the following allocation and suffix. -/
theorem initialized {mode : Bool} {invocation : Staging.Recursive.Scope} {rest : List StatementId}
    {expression : ExpressionId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some expression))
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ child reason, child < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.fault reason) after) ∨
    (∃ child tailSize value middle location bound, child < size ∧ tailSize < size ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.value value) middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location bound ∧
      PlainStatements program mode tailSize invocation nextContext ((binder.id, location) :: environment)
        bound rest finalContext outcome after) := by
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨_, reason, strict, equalContext, equalOutcome, failed⟩ | ⟨_, strict, stopped, head⟩ |
    ⟨_, tailSize, middleContext, nextEnvironment, middle, strict, tailStrict, head, tail⟩
  · obtain ⟨child, childStrict, failed⟩ := initialized_fault unique found form mono failed
    exact .inl ⟨child, reason, Nat.lt_trans childStrict strict, equalContext, equalOutcome, .fault failed⟩
  · obtain ⟨child, value, middle, location, rfl, equalContext, equalOutcome, evaluated, allocated⟩ :=
      initialized_value unique found form mono extended head
    subst finalContext
    subst outcome
    rcases stopped with impossible | rfl
    · cases impossible
    · exact .inr ⟨child, SourceExecutionSize.stepSize [], value, middle, location, after,
        Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) strict,
        by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega,
        .value evaluated, allocated, empty_trace⟩
  · obtain ⟨child, value, expressionHeap, location, rfl, equalContext, equalOutcome, evaluated, allocated⟩ :=
      initialized_value unique found form mono extended head
    subst middleContext
    cases equalOutcome
    exact .inr ⟨child, tailSize, value, expressionHeap, location, middle,
      Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) strict, tailStrict,
      .value evaluated, allocated, tail⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalInversion
