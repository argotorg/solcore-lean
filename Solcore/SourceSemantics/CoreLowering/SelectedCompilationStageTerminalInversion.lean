import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageTerminalInversion
open Frontend SourceInference
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal)

def terminalControl (outcome : Dynamic.ExpressionOutcome) : Dynamic.ControlOutcome :=
  match outcome with
  | .value value => .returned value
  | .fault reason => .fault reason

private theorem statement_returned {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {expression : ExpressionId}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment
      before id finalContext outcome after) :
    ∃ child value, child < size ∧ finalContext = context ∧ outcome = .returned value ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression value after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  refine ⟨_, ?_, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

private theorem statement_failed {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {expression : ExpressionId}
    {size : Nat} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression) ∨ node.form = .expression expression false)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment
      before id reason after) :
    ∃ child, child < size ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment before expression reason after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals
    have same := sameNode (by assumption)
    subst_vars
    obtain form | form := form <;> simp_all
  all_goals
    refine ⟨_, ?_, by assumption⟩
    exact SourceExecutionSize.child_lt_stepSize (by simp)

/-- An actual terminal function trace exposes its exact expression child,
strictly below the original size, with unchanged context and final heap. -/
theorem child_of_body {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {expression : ExpressionId} {statements : List StatementId}
    {size : Nat} {control : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source)
    (terminal : Terminal source expression statements)
    (trace : RecursiveNamedCallBounds.FunctionOutcome program size context evidence source environment
      before statements finalContext control after) :
    ∃ child outcome, child < size ∧ finalContext = context ∧ control = terminalControl outcome ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context evidence source environment
        before expression outcome after := by
  cases terminal with
  | @returning id node rest found form =>
    have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
      intro other contains
      exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    cases trace with
    | control executed =>
      cases executed with
      | tailExpression contains otherForm evaluated =>
        cases sameNode contains
        rw [form] at otherForm
        cases otherForm
      | singleton _ _ head | terminal head _ =>
        obtain ⟨child, value, strict, rfl, rfl, evaluated⟩ := statement_returned unique found form head
        exact ⟨child, .value value, Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
          rfl, rfl, .value evaluated⟩
      | cons head _ =>
        obtain ⟨_, _, _, _, impossible, _⟩ := statement_returned unique found form head
        cases impossible
    | fault failed =>
      cases failed with
      | singleton head | head head =>
        obtain ⟨child, strict, failed⟩ := statement_failed unique found (.inl form) head
        exact ⟨child, .fault _, Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
          rfl, rfl, .fault failed⟩
      | tailExpression contains otherForm _ =>
        cases sameNode contains
        rw [form] at otherForm
        cases otherForm
      | tail head _ =>
        obtain ⟨_, _, _, _, impossible, _⟩ := statement_returned unique found form head
        cases impossible
  | @tail id node found form =>
    have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
      intro other contains
      exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    cases trace with
    | control executed =>
      cases executed with
      | tailExpression contains otherForm evaluated =>
        cases sameNode contains
        rw [form] at otherForm
        cases otherForm
        exact ⟨_, .value _, SourceExecutionSize.child_lt_stepSize (by simp), rfl, rfl, .value evaluated⟩
      | singleton contains notTail _ =>
        cases sameNode contains
        exact False.elim (notTail expression form)
    | fault failed =>
      cases failed with
      | singleton head =>
        obtain ⟨child, strict, failed⟩ := statement_failed unique found (.inr form) head
        exact ⟨child, .fault _, Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
          rfl, rfl, .fault failed⟩
      | tailExpression contains otherForm failed =>
        cases sameNode contains
        rw [form] at otherForm
        cases otherForm
        exact ⟨_, .fault _, SourceExecutionSize.child_lt_stepSize (by simp), rfl, rfl, .fault failed⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageTerminalInversion
