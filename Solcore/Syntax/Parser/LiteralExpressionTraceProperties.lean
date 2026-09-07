import Solcore.Syntax.Parser.CoreLiteralRejectionTraceProperties
import Solcore.Syntax.Parser.ExpressionDiagnosticTraceContracts

/-! Five unconditional expression trace contracts for the real literal leaf. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem literalExpression_eq_ok_of_ordinary
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.LiteralExpressionParses input.declarativeRemainder value after) :
    literalExpression input = .ok value { input with cursor := input.cursor + 1 } := by
  cases parsed with
  | parsed literalParsed =>
      simp only [literalExpression, bind, coreLiteral_eq_ok_of_ordinary literalParsed, pure]

theorem literalExpression_success_state_shape
    {input output : State} {value : Expr}
    (result : literalExpression input = .ok value output) :
    output = { input with cursor := input.cursor + 1 } := by
  have actual := literalExpression_eq_ok_of_ordinary (literalExpression_success_sound result)
  rw [result] at actual
  exact (Reply.ok.inj actual).2

theorem literalExpression_trace_success_sound :
    ExpressionTraceSuccessSound literalExpression DeclarativeGrammar.LiteralExpressionTraceParses := by
  intro input output value result
  refine ⟨[], ⟨literalExpression_success_sound result, rfl⟩, ?_⟩
  rw [literalExpression_success_state_shape result]
  simp only [List.append_nil, State.diagnostics]

theorem literalExpression_trace_success_complete :
    ExpressionTraceSuccessComplete literalExpression DeclarativeGrammar.LiteralExpressionTraceParses := by
  intro input value after trace traced
  rcases traced with ⟨parsed, rfl⟩
  exact ⟨_, literalExpression_eq_ok_of_ordinary parsed,
    (DeclarativeGrammar.LiteralExpressionOrdinaryParses.output_eq parsed).symm,
    by simp only [List.append_nil, State.diagnostics]⟩

theorem literalExpression_success_context : ExpressionSuccessContext literalExpression := by
  intro input output value result
  rw [literalExpression_success_state_shape result]
  exact ⟨rfl, rfl⟩

theorem literalExpression_reject_iff_coreLiteral
    {input rejected : State} {failure : Failure} :
    literalExpression input = .reject failure rejected ↔
      coreLiteral input = .reject failure rejected := by
  cases result : coreLiteral input <;>
    simp only [literalExpression, bind, result, pure, reduceCtorEq, Reply.reject.injEq, iff_self]

theorem literalExpression_trace_reject_sound :
    ExpressionTraceRejectSound literalExpression DeclarativeGrammar.LiteralExpressionTraceRejects := by
  intro input rejected failure result
  have raw := literalExpression_reject_iff_coreLiteral.mp result
  have traced := coreLiteral_reject_trace_sound raw
  exact ⟨[], traced.1, by rw [traced.2]; simp only [List.append_nil]⟩

theorem literalExpression_trace_reject_complete :
    ExpressionTraceRejectComplete literalExpression DeclarativeGrammar.LiteralExpressionTraceRejects := by
  intro input after diagnostic trace traced
  rcases coreLiteral_trace_reject_iff.mp traced with ⟨failure, result, afterEq, reportEq, rfl⟩
  exact ⟨failure, input, literalExpression_reject_iff_coreLiteral.mpr result, afterEq.symm,
    reportEq, by simp only [List.append_nil]⟩

theorem literalExpression_trace_success_iff
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.LiteralExpressionTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, literalExpression input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact literalExpression_trace_success_complete
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases literalExpression_trace_success_sound result with ⟨actualTrace, parsed, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

/-- The real expression wrapper retains the primitive's full failure and input
state, including the literal-specific expectation and all prior diagnostics. -/
theorem literalExpression_trace_reject_failure_iff
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.LiteralExpressionTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    literalExpression input = .reject failure input ∧
      after = input.declarativeRemainder ∧ trace = [] := by
  rw [literalExpression_reject_iff_coreLiteral]
  exact coreLiteral_trace_reject_failure_iff

end Solcore.Syntax.Parser.ExpressionAtomInternals
