import Solcore.Syntax.Parser.TerminatedControlSuccessTraceProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties
import Solcore.Syntax.Parser.StatementRejectionTraceContracts

/-! Exact first-failure reports for real terminated control statements.
Neither successful token consumption nor rejection commits a diagnostic. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/-- Every rejection keeps earlier events and reports precisely the first
missing required token, at the exact current-token or window-end location. -/
theorem terminatedControl_reject_reports
    (keywordValue : HardKeyword) (statementValue : StatementValue)
    {input rejected : State} {failure : Failure}
    (result : terminatedControl keywordValue statementValue input = .reject failure rejected) :
    DeclarativeGrammar.TerminatedControlStatementTraceRejects keywordValue
      input.file.id input.window.endByte input.declarativeRemainder
      rejected.declarativeRemainder failure.toDiagnostic [] ∧
      rejected.diagnostics = input.diagnostics := by
  unfold terminatedControl at result
  cases markerResult : keyword keywordValue .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have shape := acceptToken_reject_state_shape (.keyword keywordValue) .statement
        (· == .keyword keywordValue) markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      have reported := (keyword_reject_reports_iff keywordValue .statement).mpr
        ⟨failure, markerResult, rfl⟩
      exact ⟨.markerMissing reported.1 reported.2, rfl⟩
  | ok marker afterMarker =>
      have markerParsed := keyword_success_exactTokenParses keywordValue .statement markerResult
      have markerShape := (keyword_ok_tokenAt keywordValue .statement markerResult).2
      subst afterMarker
      cases semicolonResult : symbol .semicolon .statement
          { input with cursor := input.cursor + 1 } with
      | invariant error => simp [bind, markerResult, semicolonResult] at result
      | ok semicolon next => simp [bind, markerResult, semicolonResult, pure] at result
      | reject semicolonFailure semicolonRejected =>
          have shape := acceptToken_reject_state_shape (.symbol .semicolon) .statement
            (· == .symbol .semicolon) semicolonResult
          subst semicolonRejected
          simp only [bind, markerResult, semicolonResult] at result
          cases result
          have reported := (symbol_reject_reports_iff .semicolon .statement).mpr
            ⟨failure, semicolonResult, rfl⟩
          exact ⟨.semicolonMissing marker.span markerParsed reported.1 reported.2, rfl⟩

theorem terminatedControl_trace_reject_sound
    (keywordValue : HardKeyword) (statementValue : StatementValue) :
    StatementTraceRejectSound (terminatedControl keywordValue statementValue)
      (DeclarativeGrammar.TerminatedControlStatementTraceRejects keywordValue) := by
  intro input rejected failure result
  have reported := terminatedControl_reject_reports keywordValue statementValue result
  exact ⟨[], reported.1, by simpa only [List.append_nil] using reported.2⟩

/-- Each independently specified first failure executes with the same report
and retained remainder, for arbitrary incoming state and diagnostic metadata. -/
theorem terminatedControl_trace_reject_complete
    (keywordValue : HardKeyword) (statementValue : StatementValue) :
    StatementTraceRejectComplete (terminatedControl keywordValue statementValue)
      (DeclarativeGrammar.TerminatedControlStatementTraceRejects keywordValue) := by
  intro input after diagnostic trace traced
  cases traced with
  | markerMissing absent reported =>
      rcases (keyword_reject_reports_iff keywordValue .statement).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [terminatedControl, bind, result], rfl,
        reportEq, by simp only [List.append_nil]⟩
  | semicolonMissing marker markerParsed absent reported =>
      have markerResult := keyword_eq_ok_of_exactTokenParses keywordValue .statement markerParsed
      rcases markerParsed with ⟨_, rfl⟩
      rcases (symbol_reject_reports_iff .semicolon .statement
          (input := { input with cursor := input.cursor + 1 })).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, { input with cursor := input.cursor + 1 },
        by simp only [terminatedControl, bind, markerResult, result], rfl,
        reportEq, by simp only [List.append_nil, State.diagnostics]⟩

theorem terminatedControl_trace_reject_iff
    (keywordValue : HardKeyword) (statementValue : StatementValue)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TerminatedControlStatementTraceRejects keywordValue
      input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, terminatedControl keywordValue statementValue input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact terminatedControl_trace_reject_complete keywordValue statementValue
  · rintro ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
    rcases terminatedControl_trace_reject_sound keywordValue statementValue result with
      ⟨actualTrace, traced, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, reportEq, events] using traced

/-- Every failure field, rather than only the rendered diagnostic, is fixed by
the independent report. The failure itself remains outside the retained trace. -/
theorem terminatedControl_trace_reject_failure_iff
    (keywordValue : HardKeyword) (statementValue : StatementValue)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TerminatedControlStatementTraceRejects keywordValue
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, terminatedControl keywordValue statementValue input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro traced
    rcases (terminatedControl_trace_reject_iff keywordValue statementValue).mp traced with
      ⟨actual, rejected, result, afterEq, reportEq, diagnostics⟩
    have same := Failure.toDiagnostic_injective reportEq
    subst actual
    exact ⟨rejected, result, afterEq, diagnostics⟩
  · rintro ⟨rejected, result, afterEq, diagnostics⟩
    exact (terminatedControl_trace_reject_iff keywordValue statementValue).mpr
      ⟨failure, rejected, result, afterEq, rfl, diagnostics⟩

end Solcore.Syntax.Parser.ControlInternals
