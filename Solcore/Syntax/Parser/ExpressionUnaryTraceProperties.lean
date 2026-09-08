import Solcore.Syntax.DeclarativeExpressionUnaryTraceGrammar
import Solcore.Syntax.Parser.UnaryOperatorsTraceProperties

/-! Maximal unary scanning is unconditionally successful and silent, so each
postfix trace contract independently lifts to the actual unary layer. No
postfix progress, source/window frame, joint exactness, or totality premise is
needed for the four trace laws. Successful context is a separate fifth law. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {postfixTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {postfixRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionUnary_trace_success_sound
    (successSound : ParserTraceSuccessSound (expressionPostfix nested block) postfixTrace) :
    ParserTraceSuccessSound (expressionUnary nested block) (ExpressionUnaryTraceParses postfixTrace) := by
  intro input output value result
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, afterOperators, prefixResult⟩
  unfold expressionUnary at result
  simp only [prefixResult] at result
  cases childResult : expressionPostfix nested block afterOperators with
  | invariant error => simp [childResult] at result
  | reject failure rejected => simp [childResult] at result
  | ok base next =>
      simp only [childResult] at result; cases result
      rcases successSound childResult with ⟨trace, parsed, events⟩
      have frame := unaryOperators_success_context _ [] prefixResult
      refine ⟨trace, .parsed (unaryOperators_success_sound prefixResult) ?_, ?_⟩
      · simpa only [frame.1, frame.2] using parsed
      · rw [events, unaryOperators_diagnostics_eq_onSuccess _ [] prefixResult]

theorem expressionUnary_reject_trace_sound
    (rejectSound : ParserTraceRejectSound (expressionPostfix nested block) postfixRejects) :
    ParserTraceRejectSound (expressionUnary nested block) (ExpressionUnaryTraceRejects postfixRejects) := by
  intro input rejected failure result
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, afterOperators, prefixResult⟩
  unfold expressionUnary at result
  simp only [prefixResult] at result
  cases childResult : expressionPostfix nested block afterOperators with
  | invariant error => simp [childResult] at result
  | ok base next => simp [childResult] at result
  | reject actual next =>
      simp only [childResult] at result; cases result
      rcases rejectSound childResult with ⟨trace, rejection, events⟩
      have frame := unaryOperators_success_context _ [] prefixResult
      refine ⟨trace, .postfixRejected (unaryOperators_success_sound prefixResult) ?_, ?_⟩
      · simpa only [frame.1, frame.2] using rejection
      · rw [events, unaryOperators_diagnostics_eq_onSuccess _ [] prefixResult]

theorem expressionUnary_trace_success_complete
    (successComplete : ParserTraceSuccessComplete (expressionPostfix nested block) postfixTrace) :
    ParserTraceSuccessComplete (expressionUnary nested block) (ExpressionUnaryTraceParses postfixTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed prefixParsed childParsed =>
      have prefixResult := unaryOperators_trace_success_complete prefixParsed
      rcases successComplete (input := input.traceResult _ []) (by
          simpa only [State.traceResult, State.declarativeRemainder] using childParsed) with
        ⟨output, childResult, afterEq, events⟩
      refine ⟨output, ?_, afterEq, ?_⟩
      · simp only [expressionUnary, prefixResult, childResult,
          applyUnaryOperators, DeclarativeGrammar.applyUnaryOperators]
      · simpa only [State.traceResult_diagnostics, List.append_nil] using events

theorem expressionUnary_trace_reject_complete
    (rejectComplete : ParserTraceRejectComplete (expressionPostfix nested block) postfixRejects) :
    ParserTraceRejectComplete (expressionUnary nested block) (ExpressionUnaryTraceRejects postfixRejects) := by
  intro input after report trace rejection
  cases rejection with
  | postfixRejected prefixParsed childRejected =>
      have prefixResult := unaryOperators_trace_success_complete prefixParsed
      rcases rejectComplete (input := input.traceResult _ []) (by
          simpa only [State.traceResult, State.declarativeRemainder] using childRejected) with
        ⟨failure, rejected, childResult, afterEq, reportEq, events⟩
      refine ⟨failure, rejected, ?_, afterEq, reportEq, ?_⟩
      · simp only [expressionUnary, prefixResult, childResult]
      · simpa only [State.traceResult_diagnostics, List.append_nil] using events

theorem expressionUnary_trace_success_context
    (contextFrame : ParserSuccessContext (expressionPostfix nested block)) :
    ParserSuccessContext (expressionUnary nested block) := by
  intro input output value result
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, afterOperators, prefixResult⟩
  unfold expressionUnary at result
  simp only [prefixResult] at result
  cases childResult : expressionPostfix nested block afterOperators with
  | invariant error => simp [childResult] at result
  | reject failure rejected => simp [childResult] at result
  | ok base next =>
      simp only [childResult] at result; cases result
      have prefixFrame := unaryOperators_success_context _ [] prefixResult
      have childFrame := contextFrame childResult
      exact ⟨childFrame.1.trans prefixFrame.1, childFrame.2.trans prefixFrame.2⟩

end Solcore.Syntax.Parser.ExpressionInternals
