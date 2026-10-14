import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedLiftBounds

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds (PlainStatements)

/-- The original non-tail statement either stops or reaches its actual suffix.
Singleton function bodies retain their original statement result. -/
theorem head_and_tail {program : Program} {mode : Bool} {invocation : Staging.Recursive.Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ headSize reason, headSize < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      SourceExecutionSize.StatementFaults program headSize context invocation.evidence invocation.source
        environment before id reason after) ∨
    (∃ headSize, headSize < size ∧ (Dynamic.TerminalControl outcome ∨ rest = []) ∧
      SourceExecutionSize.StatementExecutes program headSize context invocation.evidence invocation.source
        environment before id finalContext outcome after) ∨
    (∃ headSize tailSize middleContext nextEnvironment middle,
      headSize < size ∧ tailSize < size ∧
      SourceExecutionSize.StatementExecutes program headSize context invocation.evidence invocation.source
        environment before id middleContext (.fallthrough nextEnvironment) middle ∧
      PlainStatements program mode tailSize invocation middleContext nextEnvironment middle
        rest finalContext outcome after) := by
  have sameNode : ∀ {other}, ContainsStatement invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases mode with
  | false =>
    change RecursiveNamedCallBounds.StatementsOutcome _ _ _ _ _ _ _ _ _ _ _ at trace
    cases trace with
    | control executed =>
      cases executed with
      | cons head tail =>
        exact .inr (.inr ⟨_, _, _, _, _, SourceExecutionSize.child_lt_stepSize (by simp),
          SourceExecutionSize.child_lt_stepSize (by simp), head, .control tail⟩)
      | terminal head stopped =>
        exact .inr (.inl ⟨_, SourceExecutionSize.child_lt_stepSize (by simp), .inl stopped, head⟩)
    | fault failed =>
      cases failed with
      | head failed =>
        exact .inl ⟨_, _, SourceExecutionSize.child_lt_stepSize (by simp), rfl, rfl, failed⟩
      | tail head failed =>
        exact .inr (.inr ⟨_, _, _, _, _, SourceExecutionSize.child_lt_stepSize (by simp),
          SourceExecutionSize.child_lt_stepSize (by simp), head, .fault failed⟩)
  | true =>
    change RecursiveNamedCallBounds.FunctionOutcome _ _ _ _ _ _ _ _ _ _ _ at trace
    cases trace with
    | control executed =>
      cases executed with
      | tailExpression actual same _ =>
        cases sameNode actual
        exact False.elim (notTail _ same)
      | singleton _ _ head =>
        exact .inr (.inl ⟨_, SourceExecutionSize.child_lt_stepSize (by simp), .inr rfl, head⟩)
      | cons head tail =>
        exact .inr (.inr ⟨_, _, _, _, _, SourceExecutionSize.child_lt_stepSize (by simp),
          SourceExecutionSize.child_lt_stepSize (by simp), head, .control tail⟩)
      | terminal head stopped =>
        exact .inr (.inl ⟨_, SourceExecutionSize.child_lt_stepSize (by simp), .inl stopped, head⟩)
    | fault failed =>
      cases failed with
      | tailExpression actual same _ =>
        cases sameNode actual
        exact False.elim (notTail _ same)
      | singleton failed | head failed =>
        exact .inl ⟨_, _, SourceExecutionSize.child_lt_stepSize (by simp), rfl, rfl, failed⟩
      | tail head failed =>
        exact .inr (.inr ⟨_, _, _, _, _, SourceExecutionSize.child_lt_stepSize (by simp),
          SourceExecutionSize.child_lt_stepSize (by simp), head, .fault failed⟩)

/-- A block restores its outer lexical context and control environment while
retaining the exact inner trace and reached heap. -/
theorem block_control {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {body : List StatementId}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block body)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source
      environment before id finalContext outcome after) :
    ∃ innerSize innerContext innerOutcome,
      innerSize < size ∧ finalContext = context ∧ outcome = Dynamic.restoreControl environment innerOutcome ∧
      SourceExecutionSize.StatementsExecute program innerSize context evidence source environment before
        body innerContext innerOutcome after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  refine ⟨_, ?_, _, _, rfl, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

theorem block_fault {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {body : List StatementId}
    {size : Nat} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block body)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source
      environment before id reason after) :
    ∃ innerSize innerContext, innerSize < size ∧
      SourceExecutionSize.StatementsFault program innerSize context evidence source environment before
        body innerContext reason after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars; simp_all
  refine ⟨_, ?_, _, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion
