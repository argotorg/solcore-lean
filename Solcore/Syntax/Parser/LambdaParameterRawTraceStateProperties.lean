import Solcore.Syntax.Parser.ComptimeLambdaParameterTraceProperties

/-! Whole-reply correspondence for both raw lambda-parameter paths. The state
reconstruction keeps every independent remainder field and every prior event;
the diagnostic-report and complete-Failure formulations are both exact. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar

private theorem raw_success_state_iff
    {parser : Parser LambdaParameter}
    {parses : SourceId → Nat → Remainder → LambdaParameter → Remainder → List ParseDiagnostic → Prop}
    (sound : ParserTraceSuccessSound parser parses) (complete : ParserTraceSuccessComplete parser parses)
    (context : ParserSuccessContext parser)
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    parses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      parser input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases complete parsed with ⟨output, result, afterEq, events⟩
    have frame := context result
    have stateEq := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact stateEq ▸ result
  · intro result
    rcases sound result with ⟨actual, parsed, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, ← traceEq] using parsed

private theorem raw_reject_state_iff
    {parser : Parser LambdaParameter}
    {rejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    (sound : ParserTraceRejectSound parser rejects) (complete : ParserTraceRejectComplete parser rejects)
    (context : ∀ {input rejected failure}, parser input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    rejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, parser input = .reject failure (input.traceResult after trace) ∧ failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases complete rejection with ⟨failure, rejected, result, afterEq, reportEq, events⟩
    have frame := context result
    have stateEq := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact ⟨failure, stateEq ▸ result, reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    rcases sound result with ⟨actual, rejection, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, reportEq, ← traceEq] using rejection

theorem ordinaryLambdaParameter_trace_success_state_iff
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    OrdinaryLambdaParameterTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      ordinaryLambdaParameter input = .ok value (input.traceResult after trace) :=
  raw_success_state_iff ordinaryLambdaParameter_trace_success_sound ordinaryLambdaParameter_trace_success_complete
    ordinaryLambdaParameter_success_context

theorem ordinaryLambdaParameter_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    OrdinaryLambdaParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, ordinaryLambdaParameter input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report :=
  raw_reject_state_iff ordinaryLambdaParameter_reject_trace_sound ordinaryLambdaParameter_trace_reject_complete
    ordinaryLambdaParameter_reject_context

theorem ordinaryLambdaParameter_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    OrdinaryLambdaParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      ordinaryLambdaParameter input = .reject failure (input.traceResult after trace) := by
  rw [ordinaryLambdaParameter_trace_reject_state_iff]
  constructor
  · rintro ⟨actual, result, reportEq⟩
    cases Failure.toDiagnostic_injective reportEq
    exact result
  · intro result
    exact ⟨failure, result, rfl⟩

theorem comptimeLambdaParameter_trace_success_state_iff
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    ComptimeLambdaParameterTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      comptimeLambdaParameter input = .ok value (input.traceResult after trace) :=
  raw_success_state_iff comptimeLambdaParameter_trace_success_sound comptimeLambdaParameter_trace_success_complete
    comptimeLambdaParameter_success_context

theorem comptimeLambdaParameter_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ComptimeLambdaParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, comptimeLambdaParameter input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report :=
  raw_reject_state_iff comptimeLambdaParameter_reject_trace_sound comptimeLambdaParameter_trace_reject_complete
    comptimeLambdaParameter_reject_context

theorem comptimeLambdaParameter_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ComptimeLambdaParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      comptimeLambdaParameter input = .reject failure (input.traceResult after trace) := by
  rw [comptimeLambdaParameter_trace_reject_state_iff]
  constructor
  · rintro ⟨actual, result, reportEq⟩
    cases Failure.toDiagnostic_injective reportEq
    exact result
  · intro result
    exact ⟨failure, result, rfl⟩

end Solcore.Syntax.Parser.LambdaParameterInternals
