import Solcore.Syntax.Parser.ExpressionAtomTraceProperties

/-! The public rewind/recovery trace reconstructs every field of both outcomes,
including the exact terminal Failure separately from committed reports. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}
  {coreTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {coreRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionAtom_trace_success_iff
    (coreSuccessSound : ParserTraceSuccessSound (expressionAtomCore nested block) coreTrace)
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreSuccessComplete : ParserTraceSuccessComplete (expressionAtomCore nested block) coreTrace)
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionAtomTraceParses coreTrace coreRejects input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, expressionAtom nested block input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionAtom_trace_success_complete coreSuccessComplete coreRejectComplete coreRejectFrame
  · rintro ⟨output, result, afterEq, events⟩
    rcases expressionAtom_trace_success_sound coreSuccessSound coreRejectSound coreRejectFrame result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem expressionAtom_trace_reject_iff
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionAtomTraceRejects coreRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, expressionAtom nested block input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionAtom_trace_reject_complete coreRejectComplete coreRejectFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases expressionAtom_reject_trace_sound coreRejectSound coreRejectFrame result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem expressionAtom_trace_reject_failure_iff
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionAtomTraceRejects coreRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, expressionAtom nested block input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [expressionAtom_trace_reject_iff coreRejectSound coreRejectComplete coreRejectFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem expressionAtom_trace_success_state_iff
    (coreSuccessSound : ParserTraceSuccessSound (expressionAtomCore nested block) coreTrace)
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreSuccessComplete : ParserTraceSuccessComplete (expressionAtomCore nested block) coreTrace)
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreSuccessFrame : ∀ {input output value}, expressionAtomCore nested block input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionAtomTraceParses coreTrace coreRejects input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      expressionAtom nested block input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases expressionAtom_trace_success_complete coreSuccessComplete coreRejectComplete coreRejectFrame parsed with ⟨output, result, afterEq, events⟩
    have frame := expressionAtom_success_source_end coreSuccessFrame coreRejectFrame result
    have same := State.eq_traceResult_of_fields frame.1
      frame.2 afterEq events
    exact same ▸ result
  · intro result
    exact (expressionAtom_trace_success_iff coreSuccessSound coreRejectSound coreSuccessComplete coreRejectComplete coreRejectFrame).mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionAtom_trace_reject_failure_state_iff
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionAtomTraceRejects coreRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      expressionAtom nested block input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases (expressionAtom_trace_reject_failure_iff coreRejectSound coreRejectComplete coreRejectFrame).mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := expressionAtom_reject_source_end coreRejectFrame result
    have same := State.eq_traceResult_of_fields frame.1
      frame.2 afterEq events
    exact same ▸ result
  · intro result
    exact (expressionAtom_trace_reject_failure_iff coreRejectSound coreRejectComplete coreRejectFrame).mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionAtom_trace_reject_state_iff
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionAtomTraceRejects coreRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, expressionAtom nested block input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases expressionAtom_trace_reject_complete coreRejectComplete coreRejectFrame rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (expressionAtom_trace_reject_failure_state_iff coreRejectSound coreRejectComplete coreRejectFrame).mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (expressionAtom_trace_reject_failure_state_iff coreRejectSound coreRejectComplete coreRejectFrame).mpr result

/-! Non-vacuous existence follows from the explicit core ordinary contract and
soundness, not from the independent joint uniqueness/disjointness laws. -/

theorem expressionAtom_exists_trace_outcome
    (coreOrdinary : Parser.Ordinary (expressionAtomCore nested block))
    (coreSuccessSound : ParserTraceSuccessSound (expressionAtomCore nested block) coreTrace)
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (input : State) :
    (∃ value output trace,
      expressionAtom nested block input = .ok value output ∧
      ExpressionAtomTraceParses coreTrace coreRejects input.file.id input.window.endByte input.declarativeRemainder
        value output.declarativeRemainder trace ∧ output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      expressionAtom nested block input = .reject failure rejected ∧
      ExpressionAtomTraceRejects coreRejects input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧ rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases expressionAtom_ordinary_of_core coreOrdinary input with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases expressionAtom_trace_success_sound coreSuccessSound coreRejectSound coreRejectFrame result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases expressionAtom_reject_trace_sound coreRejectSound coreRejectFrame result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem expressionAtomTrace_outcome_exists
    (coreOrdinary : Parser.Ordinary (expressionAtomCore nested block))
    (coreSuccessSound : ParserTraceSuccessSound (expressionAtomCore nested block) coreTrace)
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value output trace, ExpressionAtomTraceParses coreTrace coreRejects source endByte input value output trace) ∨
    (∃ rejected report trace, ExpressionAtomTraceRejects coreRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }
    tokens := input.tokens
    cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }
    diagnosticsRev := []
  }
  have remainderEq : state.declarativeRemainder = input := rfl
  rcases expressionAtom_exists_trace_outcome coreOrdinary coreSuccessSound coreRejectSound coreRejectFrame state with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, remainderEq ▸ parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, remainderEq ▸ rejection⟩

end Solcore.Syntax.Parser
