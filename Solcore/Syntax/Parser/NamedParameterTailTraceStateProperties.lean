import Solcore.Syntax.Parser.NamedParameterTailTraceProperties
import Solcore.Syntax.Parser.ParameterProperties

/-! Bidirectional tail correspondence fixes the AST, full Failure, every state
field, and the ordered diagnostic suffix. No validity or child contracts are
required. These laws concern the raw tail, not outer parameter recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

variable (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
  (errorSpan : SourceSpan)

theorem namedParameterTail_trace_success_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterTailTraceParses start marker name errorSpan input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, namedParameterTail start marker name errorSpan input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact namedParameterTail_trace_success_complete start marker name errorSpan
  · rintro ⟨output, result, afterEq, events⟩
    rcases namedParameterTail_trace_success_sound start marker name errorSpan result with
      ⟨actualTrace, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem namedParameterTail_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    NamedParameterTailTraceRejects start marker name errorSpan input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, namedParameterTail start marker name errorSpan input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact namedParameterTail_trace_reject_complete start marker name errorSpan
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases namedParameterTail_reject_trace_sound start marker name errorSpan result with
      ⟨actualTrace, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem namedParameterTail_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    NamedParameterTailTraceRejects start marker name errorSpan input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, namedParameterTail start marker name errorSpan input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro rejection
    exact ⟨_, namedParameterTail_eq_reject_of_trace start marker name errorSpan rejection,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact (namedParameterTail_trace_reject_iff start marker name errorSpan).mpr
      ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem namedParameterTail_trace_success_state_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterTailTraceParses start marker name errorSpan input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      namedParameterTail start marker name errorSpan input = .ok value (input.traceResult after trace) := by
  constructor
  · exact namedParameterTail_eq_ok_of_trace start marker name errorSpan
  · intro result
    exact (namedParameterTail_trace_success_iff start marker name errorSpan).mpr
      ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem namedParameterTail_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    NamedParameterTailTraceRejects start marker name errorSpan input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      namedParameterTail start marker name errorSpan input = .reject failure (input.traceResult after trace) := by
  constructor
  · exact namedParameterTail_eq_reject_of_trace start marker name errorSpan
  · intro result
    exact (namedParameterTail_trace_reject_failure_iff start marker name errorSpan).mpr
      ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem namedParameterTail_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    NamedParameterTailTraceRejects start marker name errorSpan input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, namedParameterTail start marker name errorSpan input =
        .reject failure (input.traceResult after trace) ∧ failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases namedParameterTail_trace_reject_complete start marker name errorSpan rejection with
      ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, namedParameterTail_eq_reject_of_trace start marker name errorSpan
      (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (namedParameterTail_trace_reject_failure_state_iff start marker name errorSpan).mpr result

theorem namedParameterTail_preservesFile :
    Parser.PreservesFile (namedParameterTail start marker name errorSpan) := by
  intro input
  cases result : namedParameterTail start marker name errorSpan input with
  | invariant error => trivial
  | ok value output =>
      rcases namedParameterTail_trace_success_sound start marker name errorSpan result with ⟨trace, parsed, _⟩
      have expected := namedParameterTail_eq_ok_of_trace start marker name errorSpan parsed
      rw [result] at expected
      rw [(Reply.ok.inj expected).2]
      rfl
  | reject failure rejected =>
      rcases namedParameterTail_reject_trace_sound start marker name errorSpan result with ⟨trace, rejection, _⟩
      have expected := namedParameterTail_eq_reject_of_trace start marker name errorSpan rejection
      rw [result] at expected
      rw [(Reply.reject.inj expected).2]
      rfl

theorem namedParameterTail_success_context :
    ParserSuccessContext (namedParameterTail start marker name errorSpan) := by
  intro input output value result
  have window := namedParameterTail_preservesTokenWindow start marker name errorSpan input
  rw [result] at window
  exact ⟨(namedParameterTail_preservesFile start marker name errorSpan).file_eq_of_ok result, window.2⟩

theorem namedParameterTail_reject_context {input rejected : State} {failure : Failure}
    (result : namedParameterTail start marker name errorSpan input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := namedParameterTail_preservesTokenWindow start marker name errorSpan input
  rw [result] at window
  exact ⟨(namedParameterTail_preservesFile start marker name errorSpan).file_eq_of_reject result, window.2⟩

end Solcore.Syntax.Parser.FunctionParameterInternals
