import Solcore.Syntax.Parser.ExpressionUnaryTraceProperties
import Solcore.Syntax.Parser.PrimitiveRejectionDiagnosticProperties

/-! Unary success and rejection correspondence use only the matching supplied
postfix soundness/completeness directions. The silent production prefix adds
no diagnostic, frame, progress, joint-exactness, or invariant-free premise. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {postfixTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {postfixRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionUnary_trace_success_iff
    (successSound : ParserTraceSuccessSound (expressionPostfix nested block) postfixTrace)
    (successComplete : ParserTraceSuccessComplete (expressionPostfix nested block) postfixTrace)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionUnaryTraceParses postfixTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, expressionUnary nested block input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionUnary_trace_success_complete successComplete
  · rintro ⟨output, result, afterEq, events⟩
    rcases expressionUnary_trace_success_sound successSound result with ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

theorem expressionUnary_trace_reject_iff
    (rejectSound : ParserTraceRejectSound (expressionPostfix nested block) postfixRejects)
    (rejectComplete : ParserTraceRejectComplete (expressionPostfix nested block) postfixRejects)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionUnaryTraceRejects postfixRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, expressionUnary nested block input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionUnary_trace_reject_complete rejectComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases expressionUnary_reject_trace_sound rejectSound result with ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem expressionUnary_trace_reject_failure_iff
    (rejectSound : ParserTraceRejectSound (expressionPostfix nested block) postfixRejects)
    (rejectComplete : ParserTraceRejectComplete (expressionPostfix nested block) postfixRejects)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionUnaryTraceRejects postfixRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, expressionUnary nested block input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [expressionUnary_trace_reject_iff rejectSound rejectComplete]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionInternals
