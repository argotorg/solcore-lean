import Solcore.Syntax.Parser.OptionalReturnValueRejectionTraceProperties
import Solcore.Syntax.Parser.OptionalReturnValueTraceProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties
import Solcore.Syntax.Parser.StatementRejectionTraceContracts

/-! Exact return-statement rejection keeps all expression events before the
first failure and leaves its full report uncommitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {expression : Parser Expr}
  {expressionTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

/-- The failure is exactly keyword, value, or mandatory-semicolon rejection.
Expression success retains source and byte context for the final report. -/
theorem returnStatement_reject_trace_sound
    (successSound : ExpressionTraceSuccessSound expression expressionTrace)
    (rejectSound : ExpressionTraceRejectSound expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression) :
    StatementTraceRejectSound (returnStatement expression)
      (DeclarativeGrammar.ReturnStatementTraceRejects expressionTrace expressionRejects) := by
  intro input rejected failure result
  unfold returnStatement at result
  cases markerResult : keyword .returnKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have shape := acceptToken_reject_state_shape (.keyword .returnKw) .statement
        (· == .keyword .returnKw) markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      have reported := (keyword_reject_reports_iff .returnKw .statement).mpr
        ⟨failure, markerResult, rfl⟩
      exact ⟨[], .markerRejected reported.1 reported.2, by simp⟩
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .returnKw .statement markerResult
      have markerShape := (keyword_ok_tokenAt .returnKw .statement markerResult).2
      cases valueResult : StatementSimpleInternals.optionalReturnValue expression afterMarker with
      | invariant error => simp [valueResult] at result
      | reject valueFailure valueRejected =>
          simp only [valueResult] at result
          cases result
          rcases StatementSimpleInternals.optionalReturnValue_reject_trace_sound rejectSound valueResult with
            ⟨trace, rejection, diagnostics⟩
          refine ⟨trace, .valueRejected marker.span markerParsed ?_, ?_⟩
          · simpa only [markerShape] using rejection
          · simpa only [markerShape, State.diagnostics] using diagnostics
      | ok value afterValue =>
          simp only [valueResult] at result
          cases semicolonResult : symbol .semicolon .statement afterValue with
          | invariant error => simp [semicolonResult] at result
          | ok semicolon output => simp [semicolonResult, pure] at result
          | reject semicolonFailure semicolonRejected =>
              have shape := acceptToken_reject_state_shape (.symbol .semicolon) .statement
                (· == .symbol .semicolon) semicolonResult
              subst semicolonRejected
              simp only [semicolonResult] at result
              cases result
              rcases StatementSimpleInternals.optionalReturnValue_success_trace_sound successSound valueResult with
                ⟨trace, valueParsed, diagnostics⟩
              have frame := StatementSimpleInternals.optionalReturnValue_success_context_eq contextFrame valueResult
              have reported := (symbol_reject_reports_iff .semicolon .statement).mpr
                ⟨failure, semicolonResult, rfl⟩
              refine ⟨trace, .semicolonRejected (value := value)
                marker.span markerParsed ?_ reported.1 ?_, ?_⟩
              · simpa only [markerShape] using valueParsed
              · simpa only [frame.1, frame.2, markerShape] using reported.2
              · simpa only [markerShape, State.diagnostics] using diagnostics

end Solcore.Syntax.Parser
