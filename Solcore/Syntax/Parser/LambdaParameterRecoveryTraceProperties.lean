import Solcore.Syntax.DeclarativeLambdaParameterRecoveryTraceProperties
import Solcore.Syntax.Parser.ParameterRecoveryTraceProperties

/-! Lambda recovery retags only the recovered error AST. Exact function
recovery supplies its whole state, events, complete Failure, and unconditional
ordinary outcome. No caller report is committed or re-emitted by this wrapper. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar FunctionParameterInternals

theorem recoverLambdaParameter_trace_success_sound :
    ParserTraceSuccessSound recoverLambdaParameter LambdaParameterRecoveryTraceParses := by
  intro input output value result
  unfold recoverLambdaParameter at result
  cases recovered : recoverParameter input with
  | invariant error => simp [recovered] at result
  | reject failure rejected => simp [recovered] at result
  | ok parameter next =>
      simp only [recovered] at result
      cases result
      rcases recoverParameter_trace_success_sound recovered with ⟨trace, parsed, events⟩
      exact ⟨trace, .recovered parsed, events⟩

theorem recoverLambdaParameter_reject_trace_sound :
    ParserTraceRejectSound recoverLambdaParameter LambdaParameterRecoveryTraceRejects := by
  intro input rejected failure result
  unfold recoverLambdaParameter at result
  cases recovered : recoverParameter input with
  | invariant error => simp [recovered] at result
  | ok parameter next => simp [recovered] at result
  | reject actual next =>
      simp only [recovered] at result
      cases result
      exact recoverParameter_reject_trace_sound recovered

theorem recoverLambdaParameter_trace_success_state_iff
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterRecoveryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      recoverLambdaParameter input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    cases parsed with
    | recovered recovery =>
        simp only [recoverLambdaParameter, recoverParameter_trace_success_state_iff.mp recovery]
  · intro result
    rcases recoverLambdaParameter_trace_success_sound result with ⟨actual, parsed, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, ← traceEq] using parsed

theorem recoverLambdaParameter_trace_reject_failure_state_iff
    {input : State} {failure : Failure} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      recoverLambdaParameter input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    simp only [recoverLambdaParameter, recoverParameter_trace_reject_failure_state_iff.mp rejection]
  · intro result
    rcases recoverLambdaParameter_reject_trace_sound result with ⟨actual, rejection, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, ← traceEq] using rejection

theorem recoverLambdaParameter_trace_reject_state_iff
    {input : State} {report : ParseDiagnostic} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, recoverLambdaParameter input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases recoverParameter_trace_reject_complete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, recoverLambdaParameter_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ recoverLambdaParameter_trace_reject_failure_state_iff.mpr result

theorem recoverLambdaParameter_trace_success_complete :
    ParserTraceSuccessComplete recoverLambdaParameter LambdaParameterRecoveryTraceParses := by
  intro input value after trace parsed
  exact ⟨_, recoverLambdaParameter_trace_success_state_iff.mp parsed,
    input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem recoverLambdaParameter_trace_reject_complete :
    ParserTraceRejectComplete recoverLambdaParameter LambdaParameterRecoveryTraceRejects := by
  intro input after report trace rejection
  rcases recoverLambdaParameter_trace_reject_state_iff.mp rejection with ⟨failure, result, reportEq⟩
  exact ⟨failure, _, result, input.traceResult_declarativeRemainder after trace, reportEq,
    input.traceResult_diagnostics after trace⟩

theorem recoverLambdaParameter_preservesFile : Parser.PreservesFile recoverLambdaParameter := by
  intro input
  unfold recoverLambdaParameter
  cases result : recoverParameter input with
  | invariant error => trivial
  | ok parameter next => exact recoverParameter_preservesFile.file_eq_of_ok result
  | reject failure rejected => exact recoverParameter_preservesFile.file_eq_of_reject result

theorem recoverLambdaParameter_success_context : ParserSuccessContext recoverLambdaParameter := by
  intro input output value result
  have window := recoverLambdaParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨recoverLambdaParameter_preservesFile.file_eq_of_ok result, window.2⟩

theorem recoverLambdaParameter_reject_context {input rejected : State} {failure : Failure}
    (result : recoverLambdaParameter input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := recoverLambdaParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨recoverLambdaParameter_preservesFile.file_eq_of_reject result, window.2⟩

theorem recoverLambdaParameter_ordinary : Parser.Ordinary recoverLambdaParameter := by
  intro input
  rcases recoverParameter_ordinary input with ⟨parameter, next, result⟩ | ⟨failure, rejected, result⟩
  · exact .inl ⟨_, next, by simp only [recoverLambdaParameter, result]; rfl⟩
  · exact .inr ⟨failure, rejected, by simp only [recoverLambdaParameter, result]⟩

theorem recoverLambdaParameter_ne_invariant (input : State) (error : ParserInvariantError) :
    recoverLambdaParameter input ≠ .invariant error := recoverLambdaParameter_ordinary.ne_invariant input error

end Solcore.Syntax.Parser.LambdaParameterInternals
