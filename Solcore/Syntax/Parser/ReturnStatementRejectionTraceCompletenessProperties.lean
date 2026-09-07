import Solcore.Syntax.Parser.ReturnStatementRejectionTraceSoundnessProperties

/-! Complete return rejection correspondence under expression contracts.
Semicolon rejection preserves successful value events before its exact report. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {expression : Parser Expr}
  {expressionTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem returnStatement_trace_reject_complete
    (successComplete : ExpressionTraceSuccessComplete expression expressionTrace)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression) :
    StatementTraceRejectComplete (returnStatement expression)
      (DeclarativeGrammar.ReturnStatementTraceRejects expressionTrace expressionRejects) := by
  intro input remainder diagnostic trace rejection
  cases rejection with
  | markerRejected absent reported =>
      rcases (keyword_reject_reports_iff .returnKw .statement).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [returnStatement, bind, result], rfl, reportEq, by simp⟩
  | valueRejected marker markerParsed valueRejected =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .returnKw .statement markerParsed
      rcases markerParsed with ⟨markerToken, rfl⟩
      rcases StatementSimpleInternals.optionalReturnValue_trace_reject_complete rejectComplete
          (input := { input with cursor := input.cursor + 1 }) valueRejected with
        ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
      exact ⟨failure, rejected, by simp only [returnStatement, bind, markerResult, result],
        afterEq, reportEq, diagnostics⟩
  | semicolonRejected marker markerParsed valueParsed absent reported =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .returnKw .statement markerParsed
      rcases markerParsed with ⟨markerToken, rfl⟩
      rcases StatementSimpleInternals.optionalReturnValue_trace_success_complete successComplete
          (input := { input with cursor := input.cursor + 1 }) valueParsed with
        ⟨afterValue, valueResult, afterEq, diagnostics⟩
      have frame := StatementSimpleInternals.optionalReturnValue_success_context_eq contextFrame valueResult
      have absentAtValue : DeclarativeGrammar.TokenKindAbsentAt afterValue.tokens
          afterValue.window.endIndex afterValue.cursor (.symbol .semicolon) := by
        simpa only [← afterEq, State.declarativeRemainder] using absent
      have reportedAtValue : DeclarativeGrammar.RejectAtReports afterValue.file.id afterValue.window.endByte
          { head := .symbol .semicolon, tail := [] } .statement afterValue.declarativeRemainder diagnostic := by
        simpa only [frame.1, frame.2, afterEq] using reported
      rcases (symbol_reject_reports_iff .semicolon .statement).mp ⟨absentAtValue, reportedAtValue⟩ with
        ⟨failure, semicolonResult, reportEq⟩
      exact ⟨failure, afterValue, by
        simp only [returnStatement, bind, markerResult, valueResult, semicolonResult],
        afterEq, reportEq, diagnostics⟩

theorem returnStatement_trace_reject_iff
    (successSound : ExpressionTraceSuccessSound expression expressionTrace)
    (rejectSound : ExpressionTraceRejectSound expression expressionRejects)
    (successComplete : ExpressionTraceSuccessComplete expression expressionTrace)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression)
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ReturnStatementTraceRejects expressionTrace expressionRejects
      input.file.id input.window.endByte input.declarativeRemainder remainder diagnostic trace ↔
    ∃ failure rejected, returnStatement expression input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact returnStatement_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
    rcases returnStatement_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, reportEq, events] using rejection

/-- The independent diagnostic fixes every field of the uncommitted failure,
while preserving the complete remainder and preceding diagnostic suffix. -/
theorem returnStatement_trace_reject_failure_iff
    (successSound : ExpressionTraceSuccessSound expression expressionTrace)
    (rejectSound : ExpressionTraceRejectSound expression expressionRejects)
    (successComplete : ExpressionTraceSuccessComplete expression expressionTrace)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression)
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ReturnStatementTraceRejects expressionTrace expressionRejects
      input.file.id input.window.endByte input.declarativeRemainder remainder failure.toDiagnostic trace ↔
    ∃ rejected, returnStatement expression input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [returnStatement_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, diagnostics⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, diagnostics⟩
  · rintro ⟨rejected, result, afterEq, diagnostics⟩
    exact ⟨failure, rejected, result, afterEq, rfl, diagnostics⟩

end Solcore.Syntax.Parser
