import Solcore.Syntax.Parser.LambdaParameterCoreTraceProperties

/-! Exact remainder/suffix formulations and non-vacuous outcome existence for
the non-recovering lambda-parameter core. Existence uses ordinary execution
and soundness, not independent uniqueness or success/rejection disjointness. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar

theorem lambdaParameterCore_trace_success_iff
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterCoreTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      ∃ output, lambdaParameterCore input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact lambdaParameterCore_trace_success_complete
  · rintro ⟨output, result, afterEq, events⟩
    rcases lambdaParameterCore_trace_success_sound result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem lambdaParameterCore_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    LambdaParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure rejected, lambdaParameterCore input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact lambdaParameterCore_trace_reject_complete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases lambdaParameterCore_reject_trace_sound result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem lambdaParameterCore_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    LambdaParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      ∃ rejected, lambdaParameterCore input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro rejection
    exact ⟨_, lambdaParameterCore_trace_reject_failure_state_iff.mp rejection,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact lambdaParameterCore_trace_reject_iff.mpr ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem lambdaParameterCore_exists_trace_outcome (input : State) :
    (∃ value output trace,
      lambdaParameterCore input = .ok value output ∧
      LambdaParameterCoreTraceParses input.file.id input.window.endByte input.declarativeRemainder
        value output.declarativeRemainder trace ∧ output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      lambdaParameterCore input = .reject failure rejected ∧
      LambdaParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧ rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases lambdaParameterCore_ordinary_unrestricted input with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases lambdaParameterCore_trace_success_sound result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases lambdaParameterCore_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem lambdaParameterCoreTrace_outcome_exists (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value output trace, LambdaParameterCoreTraceParses source endByte input value output trace) ∨
    (∃ rejected report trace, LambdaParameterCoreTraceRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }
    tokens := input.tokens
    cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }
    diagnosticsRev := []
  }
  have remainderEq : state.declarativeRemainder = input := rfl
  rcases lambdaParameterCore_exists_trace_outcome state with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, remainderEq ▸ parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, remainderEq ▸ rejection⟩

end Solcore.Syntax.Parser.LambdaParameterInternals
