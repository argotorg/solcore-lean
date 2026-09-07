import Solcore.Syntax.Parser.ExpressionAtomRecoveryTraceStateProperties
import Solcore.Syntax.DeclarativeExpressionAtomRecoveryTraceProperties
import Solcore.Syntax.Parser.PrimitiveRejectionDiagnosticProperties
import Solcore.Syntax.Parser.DiagnosticTraceCompletenessFromSoundnessProperties

/-! Standalone recovery has unrestricted exact trace contracts. Completeness
uses ordinary execution, not existence from the independent joint specification.
The caller's earlier failure report is neither reconstructed nor re-emitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

theorem recoverAtom_trace_success_sound :
    ParserTraceSuccessSound recoverAtom ExpressionAtomRecoveryTraceParses := by
  intro input output value result
  exact ⟨[expressionAtomRecoveryTraceEvent value.span],
    ⟨recoverAtom_success_ordinary_sound result, rfl⟩, (recoverAtom_success_frame result).2⟩

theorem recoverAtom_reject_trace_sound :
    ParserTraceRejectSound recoverAtom ExpressionAtomRecoveryTraceRejects := by
  intro input rejected failure result
  have ordinary := recoverAtom_reject_ordinary_sound result
  rcases recoverAtom_reject_shape result with ⟨rfl, reported⟩
  exact ⟨[], ⟨ordinary, (rejectAt_reject_reports _ .expression reported).1, rfl⟩, by simp⟩

theorem recoverAtom_trace_success_complete :
    ParserTraceSuccessComplete recoverAtom ExpressionAtomRecoveryTraceParses :=
  trace_success_complete_of_sound recoverAtom_trace_success_sound recoverAtom_reject_trace_sound
    (fun _ _ => expressionAtomRecoveryTraceExactOutcomeSpec) recoverAtom_ne_invariant

theorem recoverAtom_trace_reject_complete :
    ParserTraceRejectComplete recoverAtom ExpressionAtomRecoveryTraceRejects :=
  trace_reject_complete_of_sound recoverAtom_trace_success_sound recoverAtom_reject_trace_sound
    (fun _ _ => expressionAtomRecoveryTraceExactOutcomeSpec) recoverAtom_ne_invariant

theorem recoverAtom_trace_success_iff
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionAtomRecoveryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, recoverAtom input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact recoverAtom_trace_success_complete
  · rintro ⟨output, result, afterEq, events⟩
    rcases recoverAtom_trace_success_sound result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem recoverAtom_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionAtomRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, recoverAtom input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact recoverAtom_trace_reject_complete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases recoverAtom_reject_trace_sound result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem recoverAtom_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionAtomRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, recoverAtom input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [recoverAtom_trace_reject_iff]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem recoverAtom_trace_success_state_iff
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionAtomRecoveryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      recoverAtom input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases recoverAtom_trace_success_complete parsed with ⟨output, result, afterEq, events⟩
    have frame := recoverAtom_success_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact recoverAtom_trace_success_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem recoverAtom_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionAtomRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      recoverAtom input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases recoverAtom_trace_reject_failure_iff.mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := recoverAtom_reject_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact recoverAtom_trace_reject_failure_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem recoverAtom_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionAtomRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, recoverAtom input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases recoverAtom_trace_reject_complete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, recoverAtom_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ recoverAtom_trace_reject_failure_state_iff.mpr result

end Solcore.Syntax.Parser.ExpressionAtomInternals
