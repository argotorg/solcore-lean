import Solcore.Syntax.Parser.ParameterRecoveryTraceStateProperties
import Solcore.Syntax.Parser.PrimitiveRejectionDiagnosticProperties
import Solcore.Syntax.Parser.DiagnosticTraceCompletenessFromSoundnessProperties

/-! Standalone recovery has unrestricted exact trace contracts. Completeness
uses ordinary execution, not existence from the independent joint specification.
The caller's earlier failure report is neither reconstructed nor re-emitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

theorem recoverParameter_trace_success_sound :
    ParserTraceSuccessSound recoverParameter FunctionParameterRecoveryTraceParses := by
  intro input output value result
  exact ⟨[parameterRecoveryTraceEvent value.span],
    ⟨recoverParameter_success_ordinary_sound result, rfl⟩, (recoverParameter_success_frame result).2⟩

theorem recoverParameter_reject_trace_sound :
    ParserTraceRejectSound recoverParameter FunctionParameterRecoveryTraceRejects := by
  intro input rejected failure result
  have ordinary := recoverParameter_reject_ordinary_sound result
  rcases recoverParameter_reject_shape result with ⟨rfl, reported⟩
  exact ⟨[], ⟨ordinary, (rejectAt_reject_reports _ .parameter reported).1, rfl⟩, by simp⟩

theorem recoverParameter_trace_success_complete :
    ParserTraceSuccessComplete recoverParameter FunctionParameterRecoveryTraceParses :=
  trace_success_complete_of_sound recoverParameter_trace_success_sound recoverParameter_reject_trace_sound
    (fun _ _ => functionParameterRecoveryTraceExactOutcomeSpec) recoverParameter_ne_invariant

theorem recoverParameter_trace_reject_complete :
    ParserTraceRejectComplete recoverParameter FunctionParameterRecoveryTraceRejects :=
  trace_reject_complete_of_sound recoverParameter_trace_success_sound recoverParameter_reject_trace_sound
    (fun _ _ => functionParameterRecoveryTraceExactOutcomeSpec) recoverParameter_ne_invariant

theorem recoverParameter_trace_success_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    FunctionParameterRecoveryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, recoverParameter input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact recoverParameter_trace_success_complete
  · rintro ⟨output, result, afterEq, events⟩
    rcases recoverParameter_trace_success_sound result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem recoverParameter_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    FunctionParameterRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, recoverParameter input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact recoverParameter_trace_reject_complete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases recoverParameter_reject_trace_sound result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem recoverParameter_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    FunctionParameterRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, recoverParameter input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [recoverParameter_trace_reject_iff]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem recoverParameter_trace_success_state_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    FunctionParameterRecoveryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      recoverParameter input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases recoverParameter_trace_success_complete parsed with ⟨output, result, afterEq, events⟩
    have frame := recoverParameter_success_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact recoverParameter_trace_success_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem recoverParameter_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    FunctionParameterRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      recoverParameter input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases recoverParameter_trace_reject_failure_iff.mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := recoverParameter_reject_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact recoverParameter_trace_reject_failure_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem recoverParameter_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    FunctionParameterRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, recoverParameter input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases recoverParameter_trace_reject_complete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, recoverParameter_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ recoverParameter_trace_reject_failure_state_iff.mpr result

end Solcore.Syntax.Parser.FunctionParameterInternals
