import Solcore.Syntax.Parser.ExpressionAtomDispatchSuccessTraceProperties
import Solcore.Syntax.Parser.ExpressionAtomDispatchRejectionTraceProperties
import Solcore.Syntax.Parser.DiagnosticTraceStateProperties

/-! Exact trace suffixes and complete State reconstruction for one atom-core
layer. Rejected States need an explicit file/end-byte frame, not preservation
of the token carrier or end index. No trace outcome existence is inferred. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {elementTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionAtomCore_trace_success_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceSuccessSound block blockTrace)
    (blockComplete : ParserTraceSuccessComplete block blockTrace)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionAtomDispatchTraceParses elementTrace blockTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, expressionAtomCore nested block input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionAtomCore_trace_success_complete successComplete contextFrame blockComplete
  · rintro ⟨output, result, afterEq, events⟩
    rcases expressionAtomCore_trace_success_sound successSound contextFrame blockSound result with
      ⟨actual, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

theorem expressionAtomCore_trace_reject_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceRejectSound block blockRejects)
    (blockComplete : ParserTraceRejectComplete block blockRejects)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionAtomDispatchTraceRejects elementTrace elementRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, expressionAtomCore nested block input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionAtomCore_trace_reject_complete successComplete rejectComplete contextFrame blockComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases expressionAtomCore_reject_trace_sound successSound rejectSound contextFrame blockSound result with
      ⟨actual, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem expressionAtomCore_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceRejectSound block blockRejects)
    (blockComplete : ParserTraceRejectComplete block blockRejects)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionAtomDispatchTraceRejects elementTrace elementRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, expressionAtomCore nested block input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [expressionAtomCore_trace_reject_iff successSound rejectSound successComplete rejectComplete
    contextFrame blockSound blockComplete]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem expressionAtomCore_trace_success_state_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceSuccessSound block blockTrace)
    (blockComplete : ParserTraceSuccessComplete block blockTrace)
    (blockFrame : ParserSuccessContext block)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionAtomDispatchTraceParses elementTrace blockTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      expressionAtomCore nested block input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases expressionAtomCore_trace_success_complete successComplete contextFrame blockComplete parsed with
      ⟨output, result, afterEq, events⟩
    have frame := expressionAtomCore_trace_success_context contextFrame blockFrame result
    exact State.eq_traceResult_of_fields frame.1 (congrArg TokenWindow.endByte frame.2) afterEq events ▸ result
  · intro result
    exact (expressionAtomCore_trace_success_iff successSound successComplete contextFrame blockSound blockComplete).mpr
      ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionAtomCore_trace_reject_failure_state_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceRejectSound block blockRejects)
    (blockComplete : ParserTraceRejectComplete block blockRejects)
    (rejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionAtomDispatchTraceRejects elementTrace elementRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      expressionAtomCore nested block input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases (expressionAtomCore_trace_reject_failure_iff successSound rejectSound successComplete rejectComplete
      contextFrame blockSound blockComplete).mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := rejectFrame result
    exact State.eq_traceResult_of_fields frame.1 frame.2 afterEq events ▸ result
  · intro result
    exact (expressionAtomCore_trace_reject_failure_iff successSound rejectSound successComplete rejectComplete
      contextFrame blockSound blockComplete).mpr
        ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionAtomCore_trace_reject_state_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceRejectSound block blockRejects)
    (blockComplete : ParserTraceRejectComplete block blockRejects)
    (rejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionAtomDispatchTraceRejects elementTrace elementRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, expressionAtomCore nested block input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases expressionAtomCore_trace_reject_complete successComplete rejectComplete contextFrame blockComplete rejection with
      ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (expressionAtomCore_trace_reject_failure_state_iff successSound rejectSound successComplete rejectComplete
      contextFrame blockSound blockComplete rejectFrame).mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (expressionAtomCore_trace_reject_failure_state_iff successSound rejectSound successComplete rejectComplete
      contextFrame blockSound blockComplete rejectFrame).mpr result

end Solcore.Syntax.Parser.ExpressionAtomInternals
