import Solcore.Syntax.Parser.NamedParameterTraceProperties

/-! The public rewind/recovery trace reconstructs every field of both outcomes,
including the exact terminal Failure separately from committed reports. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

theorem namedParameter_trace_success_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, namedParameter input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact namedParameter_trace_success_complete
  · rintro ⟨output, result, afterEq, events⟩
    rcases namedParameter_trace_success_sound result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem namedParameter_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    NamedParameterTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, namedParameter input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact namedParameter_trace_reject_complete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases namedParameter_reject_trace_sound result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem namedParameter_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    NamedParameterTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, namedParameter input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [namedParameter_trace_reject_iff]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem namedParameter_trace_success_state_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      namedParameter input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases namedParameter_trace_success_complete parsed with ⟨output, result, afterEq, events⟩
    have frame := namedParameter_success_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact namedParameter_trace_success_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem namedParameter_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    NamedParameterTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      namedParameter input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases namedParameter_trace_reject_failure_iff.mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := namedParameter_reject_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact namedParameter_trace_reject_failure_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem namedParameter_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    NamedParameterTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, namedParameter input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases namedParameter_trace_reject_complete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, namedParameter_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ namedParameter_trace_reject_failure_state_iff.mpr result

/-! Non-vacuous existence follows from unrestricted ordinary execution and
soundness, not from the independent joint uniqueness/disjointness laws. -/

theorem namedParameter_exists_trace_outcome (input : State) :
    (∃ value output trace,
      namedParameter input = .ok value output ∧
      NamedParameterTraceParses input.file.id input.window.endByte input.declarativeRemainder
        value output.declarativeRemainder trace ∧ output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      namedParameter input = .reject failure rejected ∧
      NamedParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧ rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases namedParameter_ordinary_unrestricted input with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases namedParameter_trace_success_sound result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases namedParameter_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem namedParameterTrace_outcome_exists (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value output trace, NamedParameterTraceParses source endByte input value output trace) ∨
    (∃ rejected report trace, NamedParameterTraceRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }
    tokens := input.tokens
    cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }
    diagnosticsRev := []
  }
  have remainderEq : state.declarativeRemainder = input := rfl
  rcases namedParameter_exists_trace_outcome state with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, remainderEq ▸ parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, remainderEq ▸ rejection⟩

end Solcore.Syntax.Parser
