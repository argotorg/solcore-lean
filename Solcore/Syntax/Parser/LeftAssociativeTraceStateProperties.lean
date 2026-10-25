import Solcore.Syntax.Parser.LeftAssociativeTraceCorrespondenceProperties
import Solcore.Syntax.Parser.LeftAssociativeTraceContextProperties
import Solcore.Syntax.Parser.DiagnosticTraceStateProperties

/-! Whole-State left-associative correspondence preserves every traced token,
cursor, endIndex, and ordered event. Only file/endByte frames reconstruct the
untraced fields; successful or rejected children may replace the token carrier
or numeric window. Pointwise invariant exclusion remains explicit. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

variable {operand : Parser Expr}
  {operandTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {operandRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem leftAssociative_trace_success_state_iff_of_ne_invariant
    (successSound : ParserTraceSuccessSound operand operandTrace)
    (rejectSound : ParserTraceRejectSound operand operandRejects)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (precedence : Nat) {input : State}
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, leftAssociative operand precedence input ≠ .invariant error)
    {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    LeftAssociativeTraceParses operandTrace precedence input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      leftAssociative operand precedence input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases (leftAssociative_trace_success_iff_of_ne_invariant successSound rejectSound successFrame
      precedence outcomes invariantFree).mp parsed with ⟨output, result, afterEq, events⟩
    have frame := leftAssociative_success_context_of_windowProjection successFrame precedence result
    exact State.eq_traceResult_of_fields frame.1 frame.2 afterEq events ▸ result
  · intro result
    exact (leftAssociative_trace_success_iff_of_ne_invariant successSound rejectSound successFrame
      precedence outcomes invariantFree).mpr
        ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem leftAssociative_trace_reject_failure_state_iff_of_ne_invariant
    (successSound : ParserTraceSuccessSound operand operandTrace)
    (rejectSound : ParserTraceRejectSound operand operandRejects)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (rejectFrame : ∀ {input rejected failure}, operand input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (precedence : Nat) {input : State}
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, leftAssociative operand precedence input ≠ .invariant error)
    {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    LeftAssociativeTraceRejects operandTrace operandRejects precedence input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      leftAssociative operand precedence input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases (leftAssociative_trace_reject_failure_iff_of_ne_invariant successSound rejectSound successFrame
      precedence outcomes invariantFree).mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := leftAssociative_reject_context_of_windowProjection successFrame rejectFrame precedence result
    exact State.eq_traceResult_of_fields frame.1 frame.2 afterEq events ▸ result
  · intro result
    exact (leftAssociative_trace_reject_failure_iff_of_ne_invariant successSound rejectSound successFrame
      precedence outcomes invariantFree).mpr
        ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem leftAssociative_trace_reject_state_iff_of_ne_invariant
    (successSound : ParserTraceSuccessSound operand operandTrace)
    (rejectSound : ParserTraceRejectSound operand operandRejects)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (rejectFrame : ∀ {input rejected failure}, operand input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (precedence : Nat) {input : State}
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, leftAssociative operand precedence input ≠ .invariant error)
    {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    LeftAssociativeTraceRejects operandTrace operandRejects precedence input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, leftAssociative operand precedence input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases (leftAssociative_trace_reject_iff_of_ne_invariant successSound rejectSound successFrame
      precedence outcomes invariantFree).mp rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (leftAssociative_trace_reject_failure_state_iff_of_ne_invariant successSound rejectSound
      successFrame rejectFrame precedence outcomes invariantFree).mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (leftAssociative_trace_reject_failure_state_iff_of_ne_invariant successSound rejectSound
      successFrame rejectFrame precedence outcomes invariantFree).mpr result

end Solcore.Syntax.Parser.ExpressionInternals
