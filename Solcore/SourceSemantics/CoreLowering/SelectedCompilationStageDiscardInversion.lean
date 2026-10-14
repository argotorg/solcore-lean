import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedLiftBounds

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDiscardInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds

private theorem statement_value {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {expression : ExpressionId} {semicolon : Bool}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment
      before id finalContext outcome after) :
    ∃ child value, size = SourceExecutionSize.stepSize [child] ∧ finalContext = context ∧
      outcome = .fallthrough environment ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment
        before expression value after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  exact ⟨_, rfl, _, by assumption⟩

private theorem statement_fault {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {expression : ExpressionId} {semicolon : Bool}
    {size : Nat} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment
      before id reason after) :
    ∃ child, child < size ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment
        before expression reason after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars
  all_goals simp_all
  refine ⟨_, ?_, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

/-- Discard executes its expression before its suffix. A singleton function
uses the actual empty suffix; a fault never executes that suffix. -/
theorem child_and_tail {program : Program} {mode semicolon : Bool} {invocation : Staging.Recursive.Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {expression : ExpressionId} {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (discarded : semicolon = true ∨ mode = false)
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ childSize reason, childSize < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program childSize context invocation.evidence invocation.source
        environment before expression (.fault reason) after) ∨
    (∃ childSize tailSize value middle, childSize < size ∧ tailSize < size ∧
      RecursiveNamedCallBounds.ExpressionOutcome program childSize context invocation.evidence invocation.source
        environment before expression (.value value) middle ∧
      PlainStatements program mode tailSize invocation context environment middle rest finalContext outcome after) := by
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
        obtain ⟨child, value, rfl, rfl, equal, evaluated⟩ := statement_value unique found form head
        cases equal
        exact .inr ⟨child, _, value, _, by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega,
          SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, .control tail⟩
      | terminal head terminal =>
        obtain ⟨_, _, _, _, equal, _⟩ := statement_value unique found form head
        rw [equal] at terminal
        cases terminal
    | fault failed =>
      cases failed with
      | head failed =>
        obtain ⟨child, strict, failed⟩ := statement_fault unique found form failed
        exact .inl ⟨child, _, Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
          rfl, rfl, .fault failed⟩
      | tail head tail =>
        obtain ⟨child, value, rfl, rfl, equal, evaluated⟩ := statement_value unique found form head
        cases equal
        exact .inr ⟨child, _, value, _, by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega,
          SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, .fault tail⟩
  | true =>
    have semicolonTrue : semicolon = true := by simpa using discarded
    subst semicolon
    change RecursiveNamedCallBounds.FunctionOutcome _ _ _ _ _ _ _ _ _ _ _ at trace
    cases trace with
    | control executed =>
      cases executed with
      | tailExpression contains otherForm evaluated =>
        cases sameNode contains
        rw [form] at otherForm
        cases otherForm
      | singleton _ _ head =>
        obtain ⟨child, value, rfl, rfl, equal, evaluated⟩ := statement_value unique found form head
        cases equal
        exact .inr ⟨child, SourceExecutionSize.stepSize [], value, _,
          by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega, by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega,
          .value evaluated, .control .nil⟩
      | cons head tail =>
        obtain ⟨child, value, rfl, rfl, equal, evaluated⟩ := statement_value unique found form head
        cases equal
        exact .inr ⟨child, _, value, _, by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega,
          SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, .control tail⟩
      | terminal head terminal =>
        obtain ⟨_, _, _, _, equal, _⟩ := statement_value unique found form head
        rw [equal] at terminal
        cases terminal
    | fault failed =>
      cases failed with
      | singleton failed | head failed =>
        obtain ⟨child, strict, failed⟩ := statement_fault unique found form failed
        exact .inl ⟨child, _, Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
          rfl, rfl, .fault failed⟩
      | tailExpression contains otherForm _ =>
        cases sameNode contains
        rw [form] at otherForm
        cases otherForm
      | tail head tail =>
        obtain ⟨child, value, rfl, rfl, equal, evaluated⟩ := statement_value unique found form head
        cases equal
        exact .inr ⟨child, _, value, _, by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega,
          SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, .fault tail⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDiscardInversion
