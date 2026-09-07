import Solcore.Syntax.Parser.NamedParameterCoreTraceProperties

/-! Exact remainder/suffix formulations and non-vacuous outcome existence for
the non-recovering function-parameter core. Existence uses ordinary execution
and soundness, not independent uniqueness or success/rejection disjointness. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

theorem namedParameterCore_trace_success_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterCoreTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      ∃ output, namedParameterCore input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact namedParameterCore_trace_success_complete
  · rintro ⟨output, result, afterEq, events⟩
    rcases namedParameterCore_trace_success_sound result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem namedParameterCore_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    NamedParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure rejected, namedParameterCore input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact namedParameterCore_trace_reject_complete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases namedParameterCore_reject_trace_sound result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem namedParameterCore_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    NamedParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      ∃ rejected, namedParameterCore input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro rejection
    exact ⟨_, namedParameterCore_trace_reject_failure_state_iff.mp rejection,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact namedParameterCore_trace_reject_iff.mpr ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem namedParameterCore_exists_trace_outcome (input : State) :
    (∃ value output trace,
      namedParameterCore input = .ok value output ∧
      NamedParameterCoreTraceParses input.file.id input.window.endByte input.declarativeRemainder
        value output.declarativeRemainder trace ∧ output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      namedParameterCore input = .reject failure rejected ∧
      NamedParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧ rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases namedParameterCore_ordinary_unrestricted input with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases namedParameterCore_trace_success_sound result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases namedParameterCore_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem namedParameterCoreTrace_outcome_exists (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value output trace, NamedParameterCoreTraceParses source endByte input value output trace) ∨
    (∃ rejected report trace, NamedParameterCoreTraceRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }
    tokens := input.tokens
    cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }
    diagnosticsRev := []
  }
  have remainderEq : state.declarativeRemainder = input := rfl
  rcases namedParameterCore_exists_trace_outcome state with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, remainderEq ▸ parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, remainderEq ▸ rejection⟩

end Solcore.Syntax.Parser.FunctionParameterInternals
