import Solcore.Syntax.Parser.TerminatedControlRejectionTraceProperties

/-! Unconditional exact traces for the real Core break and continue leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem breakStatement_trace_success_sound :
    StatementTraceSuccessSound breakStatement DeclarativeGrammar.BreakStatementTraceParses :=
  ControlInternals.terminatedControl_trace_success_sound .breakKw .breakStmt

theorem breakStatement_trace_success_complete :
    StatementTraceSuccessComplete breakStatement DeclarativeGrammar.BreakStatementTraceParses :=
  ControlInternals.terminatedControl_trace_success_complete .breakKw .breakStmt

theorem breakStatement_success_context : StatementSuccessContext breakStatement :=
  ControlInternals.terminatedControl_success_context .breakKw .breakStmt

theorem breakStatement_trace_reject_sound :
    StatementTraceRejectSound breakStatement DeclarativeGrammar.BreakStatementTraceRejects :=
  ControlInternals.terminatedControl_trace_reject_sound .breakKw .breakStmt

theorem breakStatement_trace_reject_complete :
    StatementTraceRejectComplete breakStatement DeclarativeGrammar.BreakStatementTraceRejects :=
  ControlInternals.terminatedControl_trace_reject_complete .breakKw .breakStmt

theorem continueStatement_trace_success_sound :
    StatementTraceSuccessSound continueStatement DeclarativeGrammar.ContinueStatementTraceParses :=
  ControlInternals.terminatedControl_trace_success_sound .continueKw .continueStmt

theorem continueStatement_trace_success_complete :
    StatementTraceSuccessComplete continueStatement DeclarativeGrammar.ContinueStatementTraceParses :=
  ControlInternals.terminatedControl_trace_success_complete .continueKw .continueStmt

theorem continueStatement_success_context : StatementSuccessContext continueStatement :=
  ControlInternals.terminatedControl_success_context .continueKw .continueStmt

theorem continueStatement_trace_reject_sound :
    StatementTraceRejectSound continueStatement DeclarativeGrammar.ContinueStatementTraceRejects :=
  ControlInternals.terminatedControl_trace_reject_sound .continueKw .continueStmt

theorem continueStatement_trace_reject_complete :
    StatementTraceRejectComplete continueStatement DeclarativeGrammar.ContinueStatementTraceRejects :=
  ControlInternals.terminatedControl_trace_reject_complete .continueKw .continueStmt

/-- Actual `break;` success retains the exact covering AST and remainder,
and is equivalent to the silent independent trace on any incoming state. -/
theorem breakStatement_trace_success_iff
    {input : State} {statement : Statement} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.BreakStatementTraceParses input.file.id input.window.endByte
      input.declarativeRemainder statement after trace ↔
    ∃ output, breakStatement input = .ok statement output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  ControlInternals.terminatedControl_trace_success_iff .breakKw .breakStmt

theorem continueStatement_trace_success_iff
    {input : State} {statement : Statement} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ContinueStatementTraceParses input.file.id input.window.endByte
      input.declarativeRemainder statement after trace ↔
    ∃ output, continueStatement input = .ok statement output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  ControlInternals.terminatedControl_trace_success_iff .continueKw .continueStmt

/-- The keyword or semicolon's complete first-failure report remains
uncommitted, preserving every incoming diagnostic event. -/
theorem breakStatement_trace_reject_iff
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.BreakStatementTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, breakStatement input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  ControlInternals.terminatedControl_trace_reject_iff .breakKw .breakStmt

theorem continueStatement_trace_reject_iff
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ContinueStatementTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, continueStatement input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  ControlInternals.terminatedControl_trace_reject_iff .continueKw .continueStmt

theorem breakStatement_trace_reject_failure_iff
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.BreakStatementTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, breakStatement input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  ControlInternals.terminatedControl_trace_reject_failure_iff .breakKw .breakStmt

theorem continueStatement_trace_reject_failure_iff
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ContinueStatementTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, continueStatement input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  ControlInternals.terminatedControl_trace_reject_failure_iff .continueKw .continueStmt

end Solcore.Syntax.Parser
