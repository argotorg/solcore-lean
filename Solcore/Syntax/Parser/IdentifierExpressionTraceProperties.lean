import Solcore.Syntax.Parser.ExpressionNameRejectionTraceProperties
import Solcore.Syntax.Parser.ExpressionDiagnosticTraceContracts

/-! Unconditional trace contracts for the real Boolean/identifier expression
leaf. This does not assert contracts for general recursive Core expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem identifierExpression_eq_ok_of_trace
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.IdentifierExpressionTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    identifierExpression input = .ok value { input with
      cursor := input.cursor + 1
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  cases parsed with
  | parsed nameParsed =>
      simp only [identifierExpression, bind, expressionName_eq_ok_of_trace nameParsed, pure]

theorem identifierExpression_success_state_eq_of_trace
    {input output : State} {value : Expr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (result : identifierExpression input = .ok value output)
    (parsed : DeclarativeGrammar.IdentifierExpressionTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    output = { input with
      cursor := input.cursor + 1
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  have expected := identifierExpression_eq_ok_of_trace parsed
  rw [result] at expected
  exact (Reply.ok.inj expected).2

theorem identifierExpression_trace_success_sound :
    ExpressionTraceSuccessSound identifierExpression DeclarativeGrammar.IdentifierExpressionTraceParses := by
  intro input output value result
  unfold identifierExpression at result
  cases nameResult : expressionName input with
  | invariant error => simp [bind, nameResult] at result
  | reject failure rejected => simp [bind, nameResult] at result
  | ok name next =>
      simp only [bind, nameResult, pure] at result
      cases result
      rcases expressionName_success_trace_sound nameResult with ⟨trace, parsed, events⟩
      exact ⟨trace, .parsed parsed, events⟩

theorem identifierExpression_trace_success_complete :
    ExpressionTraceSuccessComplete identifierExpression DeclarativeGrammar.IdentifierExpressionTraceParses := by
  intro input value after trace parsed
  refine ⟨_, identifierExpression_eq_ok_of_trace parsed, ?_, ?_⟩
  · cases parsed with
    | parsed nameParsed => exact nameParsed.output_eq.symm
  · simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem identifierExpression_success_context : ExpressionSuccessContext identifierExpression := by
  intro input output value result
  rcases identifierExpression_trace_success_sound result with ⟨trace, parsed, _⟩
  rw [identifierExpression_success_state_eq_of_trace result parsed]
  exact ⟨rfl, rfl⟩

theorem identifierExpression_reject_iff_expressionName
    {input rejected : State} {failure : Failure} :
    identifierExpression input = .reject failure rejected ↔
      expressionName input = .reject failure rejected := by
  cases result : expressionName input <;>
    simp only [identifierExpression, bind, result, pure, reduceCtorEq, Reply.reject.injEq, iff_self]

theorem identifierExpression_trace_reject_sound :
    ExpressionTraceRejectSound identifierExpression DeclarativeGrammar.IdentifierExpressionTraceRejects := by
  intro input rejected failure result
  have raw := identifierExpression_reject_iff_expressionName.mp result
  have traced := expressionName_reject_trace_sound raw
  exact ⟨[], traced.1, by rw [traced.2]; simp only [List.append_nil]⟩

theorem identifierExpression_trace_reject_complete :
    ExpressionTraceRejectComplete identifierExpression DeclarativeGrammar.IdentifierExpressionTraceRejects := by
  intro input after diagnostic trace traced
  rcases expressionName_trace_reject_iff.mp traced with ⟨failure, result, afterEq, reportEq, rfl⟩
  exact ⟨failure, input, identifierExpression_reject_iff_expressionName.mpr result, afterEq.symm,
    reportEq, by simp only [List.append_nil]⟩

theorem identifierExpression_trace_success_iff
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.IdentifierExpressionTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, identifierExpression input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact identifierExpression_trace_success_complete
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases identifierExpression_trace_success_sound result with ⟨actualTrace, parsed, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

theorem identifierExpression_trace_reject_failure_iff
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.IdentifierExpressionTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    identifierExpression input = .reject failure input ∧
      after = input.declarativeRemainder ∧ trace = [] := by
  rw [identifierExpression_reject_iff_expressionName]
  exact expressionName_trace_reject_failure_iff

end Solcore.Syntax.Parser.ExpressionAtomInternals
