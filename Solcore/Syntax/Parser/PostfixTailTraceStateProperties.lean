import Solcore.Syntax.Parser.PostfixTailTraceCorrespondenceProperties
import Solcore.Syntax.Parser.PostfixTailTraceContextProperties
import Solcore.Syntax.Parser.DiagnosticTraceStateProperties

/-! Fixed-fuel postfix trace correspondence reconstructs every State field.
The explicit no-invariant premise is retained: independent trace uniqueness
does not supply fuel adequacy. Rejection needs only file/endByte preservation,
so its traced token carrier and numeric end index may differ from the input. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {nested : Parser Expr}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem postfixTail_trace_success_state_iff_of_ne_invariant
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested) (block : Parser Block) (fuel : Nat) (base : Expr)
    {input : State}
    (outcomes : TraceExactOutcomeSpec nestedTrace nestedRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, postfixTail nested block fuel base input ≠ .invariant error)
    {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    PostfixTailTraceParses nestedTrace input.file.id input.window.endByte
      input.declarativeRemainder base value after trace ↔
      postfixTail nested block fuel base input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases (postfixTail_trace_success_iff_of_ne_invariant successSound rejectSound contextFrame
      block fuel base outcomes invariantFree).mp parsed with ⟨output, result, afterEq, events⟩
    have frame := postfixTail_success_context contextFrame block fuel base result
    have same := State.eq_traceResult_of_fields frame.1 (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact (postfixTail_trace_success_iff_of_ne_invariant successSound rejectSound contextFrame
      block fuel base outcomes invariantFree).mpr
        ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem postfixTail_trace_reject_failure_state_iff_of_ne_invariant
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (rejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (block : Parser Block) (fuel : Nat) (base : Expr) {input : State}
    (outcomes : TraceExactOutcomeSpec nestedTrace nestedRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, postfixTail nested block fuel base input ≠ .invariant error)
    {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
      input.declarativeRemainder base after failure.toDiagnostic trace ↔
      postfixTail nested block fuel base input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases (postfixTail_trace_reject_failure_iff_of_ne_invariant successSound rejectSound contextFrame
      block fuel base outcomes invariantFree).mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := postfixTail_reject_source_endByte contextFrame rejectFrame block fuel base result
    have same := State.eq_traceResult_of_fields frame.1 frame.2 afterEq events
    exact same ▸ result
  · intro result
    exact (postfixTail_trace_reject_failure_iff_of_ne_invariant successSound rejectSound contextFrame
      block fuel base outcomes invariantFree).mpr
        ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem postfixTail_trace_reject_state_iff_of_ne_invariant
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (rejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (block : Parser Block) (fuel : Nat) (base : Expr) {input : State}
    (outcomes : TraceExactOutcomeSpec nestedTrace nestedRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, postfixTail nested block fuel base input ≠ .invariant error)
    {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
      input.declarativeRemainder base after report trace ↔
      ∃ failure, postfixTail nested block fuel base input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases (postfixTail_trace_reject_iff_of_ne_invariant successSound rejectSound contextFrame
      block fuel base outcomes invariantFree).mp rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (postfixTail_trace_reject_failure_state_iff_of_ne_invariant successSound rejectSound
      contextFrame rejectFrame block fuel base outcomes invariantFree).mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (postfixTail_trace_reject_failure_state_iff_of_ne_invariant successSound rejectSound
      contextFrame rejectFrame block fuel base outcomes invariantFree).mpr result

end Solcore.Syntax.Parser.ExpressionAtomInternals
