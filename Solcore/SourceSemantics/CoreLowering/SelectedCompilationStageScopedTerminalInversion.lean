import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageTerminalInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedTerminalStatements

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedTerminalInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageBodyLiftBounds (terminalControl)

variable {program : Program} {source : TypedSource}
  {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {expression : ExpressionId}
  {size : Nat} {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

private theorem statement_returned (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    ∃ child value, child < size ∧ finalContext = context ∧ outcome = .returned value ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression value after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  refine ⟨_, ?_, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

private theorem statement_failed (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child, child < size ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment before expression reason after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars; simp_all
  refine ⟨_, ?_, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

private theorem statement_unit (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all

private theorem statement_unit_no_fault (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) : False := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars; simp_all

theorem nil {mode : Bool} {invocation : Staging.Recursive.Scope}
    (trace : PlainStatements program mode size invocation context environment before [] finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ after = before := by
  cases mode <;> cases trace with
  | control executed => cases executed; exact ⟨rfl, rfl, rfl⟩
  | fault failed => cases failed

theorem return_unit {mode : Bool} {invocation : Staging.Recursive.Scope} {rest : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
    (trace : PlainStatements program mode size invocation context environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨_, _, _, _, _, failed⟩ | ⟨_, _, _, head⟩ | ⟨_, _, _, _, _, _, _, head, _⟩
  · exact (statement_unit_no_fault unique found form failed).elim
  · exact statement_unit unique found form head
  · obtain ⟨_, impossible, _⟩ := statement_unit unique found form head
    cases impossible

/-- Returning statements retain the same strict expression in both lexical
modes. The function-only tail expression remains a distinct original form. -/
theorem child_of_body {mode : Bool} {invocation : Staging.Recursive.Scope} {statements : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression mode statements)
    (trace : PlainStatements program mode size invocation context environment before statements finalContext outcome after) :
    ∃ child plain, child < size ∧ finalContext = context ∧ outcome = terminalControl plain ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression plain after := by
  cases head with
  | returning rest contains form =>
    have found := lookupStatement?_complete unique contains
    rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
      (by intro expression equal; rw [form] at equal; cases equal) trace with
      ⟨_, reason, strict, rfl, rfl, failed⟩ | ⟨_, strict, _, head⟩ | ⟨_, _, _, _, _, _, _, head, _⟩
    · obtain ⟨child, childStrict, failed⟩ := statement_failed unique found form failed
      exact ⟨child, .fault reason, Nat.lt_trans childStrict strict, rfl, rfl, .fault failed⟩
    · obtain ⟨child, value, childStrict, rfl, rfl, evaluated⟩ := statement_returned unique found form head
      exact ⟨child, .value value, Nat.lt_trans childStrict strict, rfl, rfl, .value evaluated⟩
    · obtain ⟨_, _, _, _, impossible, _⟩ := statement_returned unique found form head
      cases impossible
  | tail contains form =>
    exact SelectedCompilationStageTerminalInversion.child_of_body unique
      (.tail (lookupStatement?_complete unique contains) form) trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedTerminalInversion
