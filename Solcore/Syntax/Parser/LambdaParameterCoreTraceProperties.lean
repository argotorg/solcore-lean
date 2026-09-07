import Solcore.Syntax.DeclarativeLambdaParameterCoreTraceProperties
import Solcore.Syntax.Parser.LambdaParameterRawTraceStateProperties
import Solcore.Syntax.Parser.ParameterDispatchTraceProperties

/-! Unconditional exact traces for the non-recovering lambda-parameter core.
The same independent two-token guard chooses each raw success or rejection;
the returned AST, complete State, Failure, and event order are unchanged.
Public rewind and recovery are separate stages. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar ParameterDispatchTraceInternals

theorem lambdaParameterCore_trace_success_sound :
    ParserTraceSuccessSound lambdaParameterCore LambdaParameterCoreTraceParses := by
  intro input output value result
  by_cases guard : comptimeGuard input = true
  · have present := comptimeGuard_true_iff.mp guard
    rw [lambdaParameterCore_eq_comptime_of_prefix present] at result
    rcases comptimeLambdaParameter_trace_success_sound result with ⟨trace, parsed, events⟩
    exact ⟨trace, .comptime present parsed, events⟩
  · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
    rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent] at result
    rcases ordinaryLambdaParameter_trace_success_sound result with ⟨trace, parsed, events⟩
    exact ⟨trace, .ordinary absent parsed, events⟩

theorem lambdaParameterCore_reject_trace_sound :
    ParserTraceRejectSound lambdaParameterCore LambdaParameterCoreTraceRejects := by
  intro input rejected failure result
  by_cases guard : comptimeGuard input = true
  · have present := comptimeGuard_true_iff.mp guard
    rw [lambdaParameterCore_eq_comptime_of_prefix present] at result
    rcases comptimeLambdaParameter_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact ⟨trace, .comptime present rejection, events⟩
  · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
    rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent] at result
    rcases ordinaryLambdaParameter_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact ⟨trace, .ordinary absent rejection, events⟩

theorem lambdaParameterCore_trace_success_complete :
    ParserTraceSuccessComplete lambdaParameterCore LambdaParameterCoreTraceParses := by
  intro input value after trace parsed
  cases parsed with
  | ordinary absent raw =>
      rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent]
      exact ordinaryLambdaParameter_trace_success_complete raw
  | comptime present raw =>
      rw [lambdaParameterCore_eq_comptime_of_prefix present]
      exact comptimeLambdaParameter_trace_success_complete raw

theorem lambdaParameterCore_trace_reject_complete :
    ParserTraceRejectComplete lambdaParameterCore LambdaParameterCoreTraceRejects := by
  intro input after report trace rejection
  cases rejection with
  | ordinary absent raw =>
      rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent]
      exact ordinaryLambdaParameter_trace_reject_complete raw
  | comptime present raw =>
      rw [lambdaParameterCore_eq_comptime_of_prefix present]
      exact comptimeLambdaParameter_trace_reject_complete raw

theorem lambdaParameterCore_success_context : ParserSuccessContext lambdaParameterCore := by
  intro input output value result
  have window := lambdaParameterCore_preservesTokenWindow input
  rw [result] at window
  exact ⟨lambdaParameterCore_preservesFile.file_eq_of_ok result, window.2⟩

theorem lambdaParameterCore_reject_context {input rejected : State} {failure : Failure}
    (result : lambdaParameterCore input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := lambdaParameterCore_preservesTokenWindow input
  rw [result] at window
  exact ⟨lambdaParameterCore_preservesFile.file_eq_of_reject result, window.2⟩

theorem lambdaParameterCore_trace_success_state_iff
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterCoreTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      lambdaParameterCore input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    cases parsed with
    | ordinary absent raw =>
        rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent]
        exact ordinaryLambdaParameter_trace_success_state_iff.mp raw
    | comptime present raw =>
        rw [lambdaParameterCore_eq_comptime_of_prefix present]
        exact comptimeLambdaParameter_trace_success_state_iff.mp raw
  · intro result
    by_cases guard : comptimeGuard input = true
    · have present := comptimeGuard_true_iff.mp guard
      rw [lambdaParameterCore_eq_comptime_of_prefix present] at result
      exact .comptime present (comptimeLambdaParameter_trace_success_state_iff.mpr result)
    · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
      rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent] at result
      exact .ordinary absent (ordinaryLambdaParameter_trace_success_state_iff.mpr result)

theorem lambdaParameterCore_trace_reject_failure_state_iff
    {input : State} {failure : Failure} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔ lambdaParameterCore input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    cases rejection with
    | ordinary absent raw =>
        rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent]
        exact ordinaryLambdaParameter_trace_reject_failure_state_iff.mp raw
    | comptime present raw =>
        rw [lambdaParameterCore_eq_comptime_of_prefix present]
        exact comptimeLambdaParameter_trace_reject_failure_state_iff.mp raw
  · intro result
    by_cases guard : comptimeGuard input = true
    · have present := comptimeGuard_true_iff.mp guard
      rw [lambdaParameterCore_eq_comptime_of_prefix present] at result
      exact .comptime present (comptimeLambdaParameter_trace_reject_failure_state_iff.mpr result)
    · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
      rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent] at result
      exact .ordinary absent (ordinaryLambdaParameter_trace_reject_failure_state_iff.mpr result)

theorem lambdaParameterCore_trace_reject_state_iff
    {input : State} {report : ParseDiagnostic} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, lambdaParameterCore input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases lambdaParameterCore_trace_reject_complete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, lambdaParameterCore_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ lambdaParameterCore_trace_reject_failure_state_iff.mpr result

theorem lambdaParameterCore_ordinary_unrestricted : Parser.Ordinary lambdaParameterCore := by
  intro input
  by_cases guard : comptimeGuard input = true
  · rw [lambdaParameterCore_eq_comptime_of_prefix (comptimeGuard_true_iff.mp guard)]
    exact comptimeLambdaParameter_ordinary input
  · rw [lambdaParameterCore_eq_ordinary_of_prefix_absent
      (comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard))]
    exact ordinaryLambdaParameter_ordinary input

theorem lambdaParameterCore_ne_invariant_unrestricted (input : State) (error : ParserInvariantError) :
    lambdaParameterCore input ≠ .invariant error := by
  intro failed
  rcases lambdaParameterCore_ordinary_unrestricted input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.LambdaParameterInternals
