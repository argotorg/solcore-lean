import Solcore.Syntax.Parser.CoreBlockTraceCompletenessProperties
import Solcore.Syntax.Parser.CoreBlockRejectionTraceCompletenessProperties
import Solcore.Syntax.Parser.IdentifierTraceProperties
import Solcore.Syntax.Parser.PragmaItemsContextProperties

/-! A deliberately small test-only statement parser: checked names become
unterminated expression statements. Its independent contracts quantify all
source contexts, windows, and prior diagnostics; this is not the Core parser. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxBlockIdentifierTraceContracts

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

def nameStatement (name : Identifier) : Statement := {
  span := name.span
  value := .expression { span := name.span, value := .identifier name } false
}

def checkedNameStatement : Parser Statement := fun input =>
  match identifier .statement input with
  | .ok name output => .ok (nameStatement name) output
  | .reject failure rejected => .reject failure rejected
  | .invariant error => .invariant error

inductive NameStatementTraceParses (_source : SourceId) (_endByte : Nat) :
    Remainder → Statement → Remainder → List ParseDiagnostic → Prop where
  | parsed {input output : Remainder} {name : Identifier} {trace : List ParseDiagnostic}
      (nameParsed : IdentifierTraceParses input name output trace) :
      NameStatementTraceParses _source _endByte input (nameStatement name) output trace

def NameStatementTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (diagnostic : ParseDiagnostic)
    (trace : List ParseDiagnostic) : Prop :=
  IdentifierRejects input rejected ∧
    RejectAtReports source endByte { head := .identifier, tail := [] }
      .statement rejected diagnostic ∧ trace = []

theorem checkedNameStatement_success_sound :
    StatementTraceSuccessSound checkedNameStatement NameStatementTraceParses := by
  intro input output statement result
  unfold checkedNameStatement at result
  cases nameResult : identifier .statement input with
  | reject failure rejected => simp [nameResult] at result
  | invariant error => simp [nameResult] at result
  | ok name next =>
      simp only [nameResult] at result
      cases result
      rcases identifier_success_trace_sound .statement nameResult with
        ⟨trace, parsed, diagnostics⟩
      exact ⟨trace, .parsed parsed, diagnostics⟩

theorem checkedNameStatement_success_complete :
    StatementTraceSuccessComplete checkedNameStatement NameStatementTraceParses := by
  intro input statement after trace parsed
  cases parsed with
  | parsed nameParsed =>
      rcases (identifier_trace_success_iff .statement).mp nameParsed with
        ⟨output, result, remainder, diagnostics⟩
      exact ⟨output, by simp only [checkedNameStatement, result], remainder, diagnostics⟩

theorem checkedNameStatement_success_context :
    StatementSuccessContext checkedNameStatement := by
  intro input output statement result
  unfold checkedNameStatement at result
  cases nameResult : identifier .statement input with
  | reject failure rejected => simp [nameResult] at result
  | invariant error => simp [nameResult] at result
  | ok name next =>
      simp only [nameResult] at result
      cases result
      exact identifier_success_context_eq .statement nameResult

theorem checkedNameStatement_reject_sound :
    StatementTraceRejectSound checkedNameStatement NameStatementTraceRejects := by
  intro input rejected failure result
  unfold checkedNameStatement at result
  cases nameResult : identifier .statement input with
  | ok name output => simp [nameResult] at result
  | invariant error => simp [nameResult] at result
  | reject actual output =>
      simp only [nameResult] at result
      cases result
      have stateEq := identifier_reject_state_eq .statement nameResult
      subst rejected
      have reports := (identifier_reject_reports_iff .statement).mpr ⟨failure, nameResult, rfl⟩
      exact ⟨[], ⟨.absent reports.1, reports.2, rfl⟩, by simp⟩

theorem checkedNameStatement_reject_complete :
    StatementTraceRejectComplete checkedNameStatement NameStatementTraceRejects := by
  intro input after diagnostic trace rejected
  rcases rejected with ⟨ordinary, report, rfl⟩
  cases ordinary with
  | absent missing =>
      rcases (identifier_reject_reports_iff .statement).mp ⟨missing, report⟩ with
        ⟨failure, result, diagnosticEq⟩
      exact ⟨failure, input, by simp only [checkedNameStatement, result],
        rfl, diagnosticEq, by simp⟩

end Solcore.Test.SyntaxBlockIdentifierTraceContracts
