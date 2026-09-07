import Solcore.Syntax.Parser.ComptimeNamedParameterTraceProperties

/-! Whole-reply correspondence for both raw named-parameter paths. The state
reconstruction keeps every independent remainder field and every prior event;
the diagnostic-report and complete-Failure formulations are both exact. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

private theorem raw_success_state_iff
    {parser : Parser FunctionParameter}
    {parses : SourceId → Nat → Remainder → FunctionParameter → Remainder → List ParseDiagnostic → Prop}
    (sound : ParserTraceSuccessSound parser parses) (complete : ParserTraceSuccessComplete parser parses)
    (context : ParserSuccessContext parser)
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
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
    {parser : Parser FunctionParameter}
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

theorem ordinaryNamedParameter_trace_success_state_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    OrdinaryNamedParameterTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      ordinaryNamedParameter input = .ok value (input.traceResult after trace) :=
  raw_success_state_iff ordinaryNamedParameter_trace_success_sound ordinaryNamedParameter_trace_success_complete
    ordinaryNamedParameter_success_context

theorem ordinaryNamedParameter_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    OrdinaryNamedParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, ordinaryNamedParameter input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report :=
  raw_reject_state_iff ordinaryNamedParameter_reject_trace_sound ordinaryNamedParameter_trace_reject_complete
    ordinaryNamedParameter_reject_context

theorem ordinaryNamedParameter_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    OrdinaryNamedParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      ordinaryNamedParameter input = .reject failure (input.traceResult after trace) := by
  rw [ordinaryNamedParameter_trace_reject_state_iff]
  constructor
  · rintro ⟨actual, result, reportEq⟩
    cases Failure.toDiagnostic_injective reportEq
    exact result
  · intro result
    exact ⟨failure, result, rfl⟩

theorem comptimeNamedParameter_trace_success_state_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    ComptimeNamedParameterTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      comptimeNamedParameter input = .ok value (input.traceResult after trace) :=
  raw_success_state_iff comptimeNamedParameter_trace_success_sound comptimeNamedParameter_trace_success_complete
    comptimeNamedParameter_success_context

theorem comptimeNamedParameter_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ComptimeNamedParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, comptimeNamedParameter input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report :=
  raw_reject_state_iff comptimeNamedParameter_reject_trace_sound comptimeNamedParameter_trace_reject_complete
    comptimeNamedParameter_reject_context

theorem comptimeNamedParameter_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ComptimeNamedParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      comptimeNamedParameter input = .reject failure (input.traceResult after trace) := by
  rw [comptimeNamedParameter_trace_reject_state_iff]
  constructor
  · rintro ⟨actual, result, reportEq⟩
    cases Failure.toDiagnostic_injective reportEq
    exact result
  · intro result
    exact ⟨failure, result, rfl⟩

end Solcore.Syntax.Parser.FunctionParameterInternals
