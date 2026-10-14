import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialBounds

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForSourceInversion
open Frontend SourceInference
open SelectedCompilationStageForLiftBounds SelectedCompilationStageForInitialBounds

private theorem loop_fields {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {test : ExpressionId} {body : List StatementId} {post : List ForItemForm} {size : Nat} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.ForLoopExecutes program size context evidence source environment before
      test post body finalContext outcome after) :
    finalContext = context ∧ Dynamic.restoreControl environment outcome = outcome := by
  induction size using Nat.strongRecOn generalizing before after outcome finalContext with
  | ind size ih =>
    cases trace with
    | done => exact ⟨rfl, rfl⟩
    | breaks => exact ⟨rfl, rfl⟩
    | returns => exact ⟨rfl, rfl⟩
    | nextFallthrough _ _ _ next | nextContinue _ _ _ next =>
      exact ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next

theorem control {program : Program} {invocation : Staging.Recursive.Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
    {test : ExpressionId} {items post : List ForItemForm} {body : List StatementId}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .forLoop items test post body)
    (trace : SourceExecutionSize.StatementExecutes program size context invocation.evidence invocation.source
      environment before id finalContext outcome after) :
    finalContext = context ∧
      PlainInitial program invocation context environment before items test post body size outcome after := by
  have sameNode : ∀ {other}, ContainsStatement invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  obtain ⟨sameContext, _⟩ := loop_fields (by assumption)
  subst_vars
  exact .loop (by assumption) (.control (by assumption))

theorem fault {program : Program} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
    {test : ExpressionId} {items post : List ForItemForm} {body : List StatementId}
    {size : Nat} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .forLoop items test post body)
    (trace : SourceExecutionSize.StatementFaults program size context invocation.evidence invocation.source
      environment before id reason after) :
    PlainInitial program invocation context environment before items test post body size (.fault reason) after := by
  have sameNode : ∀ {other}, ContainsStatement invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars; simp_all
  · exact .initializerFault (by assumption)
  · exact .loop (by assumption) (.fault (by assumption))

theorem fallthrough_environment {program : Program} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment nextEnvironment : Dynamic.Environment}
    {before after : Dynamic.Heap} {test : ExpressionId} {items post : List ForItemForm} {body : List StatementId}
    {size : Nat}
    (trace : PlainInitial program invocation context environment before items test post body size
      (.fallthrough nextEnvironment) after) : nextEnvironment = environment := by
  generalize same : Dynamic.ControlOutcome.fallthrough nextEnvironment = result at trace
  cases trace with
  | initializerFault => cases same
  | @loop _ _ _ _ _ outcome _ initial trace =>
    cases outcome <;> simp_all [Dynamic.restoreControl]

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForSourceInversion
