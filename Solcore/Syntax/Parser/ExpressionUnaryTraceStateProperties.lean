import Solcore.Syntax.Parser.ExpressionUnaryTraceCorrespondenceProperties
import Solcore.Syntax.Parser.DiagnosticTraceStateProperties

/-! Whole unary replies are reconstructed from the exact traced remainder.
Both successful and rejected postfix frames preserve only file/endByte; token
carriers, cursors, and numeric endIndex remain whatever the trace specifies.
Prefix scanning is unconditionally successful and preserves every other field. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {postfixTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {postfixRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

private theorem unary_success_frame
    (postfixFrame : ∀ {input output value}, expressionPostfix nested block input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    {input output : State} {value : Expr}
    (result : expressionUnary nested block input = .ok value output) :
    output.file = input.file ∧ output.window.endByte = input.window.endByte := by
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, next, prefixResult⟩
  have prefixFrame := unaryOperators_success_context (input.remainingCount + 1) [] prefixResult
  simp only [expressionUnary, prefixResult] at result
  cases postfixResult : expressionPostfix nested block next with
  | invariant error => simp [postfixResult] at result
  | reject failure rejected => simp [postfixResult] at result
  | ok base final =>
      simp only [postfixResult] at result
      cases result
      have frame := postfixFrame postfixResult
      exact ⟨frame.1.trans prefixFrame.1, frame.2.trans (congrArg TokenWindow.endByte prefixFrame.2)⟩

private theorem unary_reject_frame
    (postfixFrame : ∀ {input rejected failure}, expressionPostfix nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input rejected : State} {failure : Failure}
    (result : expressionUnary nested block input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte := by
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, next, prefixResult⟩
  have prefixFrame := unaryOperators_success_context (input.remainingCount + 1) [] prefixResult
  simp only [expressionUnary, prefixResult] at result
  cases postfixResult : expressionPostfix nested block next with
  | invariant error => simp [postfixResult] at result
  | ok base final => simp [postfixResult] at result
  | reject actual final =>
      simp only [postfixResult] at result
      cases result
      have frame := postfixFrame postfixResult
      exact ⟨frame.1.trans prefixFrame.1, frame.2.trans (congrArg TokenWindow.endByte prefixFrame.2)⟩

theorem expressionUnary_trace_success_state_iff
    (successSound : ParserTraceSuccessSound (expressionPostfix nested block) postfixTrace)
    (successComplete : ParserTraceSuccessComplete (expressionPostfix nested block) postfixTrace)
    (postfixFrame : ∀ {input output value}, expressionPostfix nested block input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionUnaryTraceParses postfixTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      expressionUnary nested block input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases (expressionUnary_trace_success_iff successSound successComplete).mp parsed with
      ⟨output, result, afterEq, events⟩
    have frame := unary_success_frame postfixFrame result
    exact State.eq_traceResult_of_fields frame.1 frame.2 afterEq events ▸ result
  · intro result
    exact (expressionUnary_trace_success_iff successSound successComplete).mpr
      ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionUnary_trace_reject_failure_state_iff
    (rejectSound : ParserTraceRejectSound (expressionPostfix nested block) postfixRejects)
    (rejectComplete : ParserTraceRejectComplete (expressionPostfix nested block) postfixRejects)
    (postfixFrame : ∀ {input rejected failure}, expressionPostfix nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionUnaryTraceRejects postfixRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      expressionUnary nested block input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases (expressionUnary_trace_reject_failure_iff rejectSound rejectComplete).mp rejection with
      ⟨rejected, result, afterEq, events⟩
    have frame := unary_reject_frame postfixFrame result
    exact State.eq_traceResult_of_fields frame.1 frame.2 afterEq events ▸ result
  · intro result
    exact (expressionUnary_trace_reject_failure_iff rejectSound rejectComplete).mpr
      ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionUnary_trace_reject_state_iff
    (rejectSound : ParserTraceRejectSound (expressionPostfix nested block) postfixRejects)
    (rejectComplete : ParserTraceRejectComplete (expressionPostfix nested block) postfixRejects)
    (postfixFrame : ∀ {input rejected failure}, expressionPostfix nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionUnaryTraceRejects postfixRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, expressionUnary nested block input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases (expressionUnary_trace_reject_iff rejectSound rejectComplete).mp rejection with
      ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (expressionUnary_trace_reject_failure_state_iff rejectSound rejectComplete postfixFrame).mp
      (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (expressionUnary_trace_reject_failure_state_iff rejectSound rejectComplete postfixFrame).mpr result

end Solcore.Syntax.Parser.ExpressionInternals
