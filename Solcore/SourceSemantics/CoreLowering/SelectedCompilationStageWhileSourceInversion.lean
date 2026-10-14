import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileLifting

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileSourceInversion
open Frontend SourceInference
open SelectedCompilationStageWhileLifting

private theorem loop_fields {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {test : ExpressionId} {body : List StatementId} {size : Nat} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.WhileExecutes program size context evidence source environment before
      test body finalContext outcome after) :
    finalContext = context ∧ Dynamic.restoreControl environment outcome = outcome := by
  induction size using Nat.strongRecOn generalizing before after outcome finalContext with
  | ind size ih =>
    cases trace with
    | done => exact ⟨rfl, rfl⟩
    | breaks => exact ⟨rfl, rfl⟩
    | returns => exact ⟨rfl, rfl⟩
    | nextFallthrough _ _ next | nextContinue _ _ next =>
      exact ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next

theorem control {program : Program} {invocation : Staging.Recursive.Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
    {test : ExpressionId} {body : List StatementId} {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .whileLoop test body)
    (trace : SourceExecutionSize.StatementExecutes program size context invocation.evidence invocation.source
      environment before id finalContext outcome after) :
    ∃ child, child < size ∧ finalContext = context ∧
      PlainWhile program child invocation context environment before test body outcome after := by
  have sameNode : ∀ {other}, ContainsStatement invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  rename_i loopContext result child iterate
  obtain ⟨rfl, restored⟩ := loop_fields iterate
  rw [restored]
  refine ⟨_, ?_, .control iterate⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

theorem fault {program : Program} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
    {test : ExpressionId} {body : List StatementId} {size : Nat} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .whileLoop test body)
    (trace : SourceExecutionSize.StatementFaults program size context invocation.evidence invocation.source
      environment before id reason after) :
    ∃ child, child < size ∧ PlainWhile program child invocation context environment before test body (.fault reason) after := by
  have sameNode : ∀ {other}, ContainsStatement invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars; simp_all
  refine ⟨_, ?_, .fault (by assumption)⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

theorem fallthrough_environment {program : Program} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment innerEnvironment : Dynamic.Environment}
    {before after : Dynamic.Heap} {test : ExpressionId} {body : List StatementId} {size : Nat}
    (trace : PlainWhile program size invocation context environment before test body (.fallthrough innerEnvironment) after) :
    innerEnvironment = environment := by
  cases trace with
  | control evaluated =>
    have same := (loop_fields evaluated).2
    exact (Dynamic.ControlOutcome.fallthrough.inj same).symm

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileSourceInversion
