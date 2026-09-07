import Solcore.Syntax.DeclarativeNamedParameterCoreTraceProperties
import Solcore.Syntax.Parser.NamedParameterRawTraceStateProperties
import Solcore.Syntax.Parser.ParameterDispatchTraceProperties

/-! Unconditional exact traces for the non-recovering function-parameter core.
The same independent two-token guard chooses each raw success or rejection;
the returned AST, complete State, Failure, and event order are unchanged.
Public rewind and recovery are separate stages. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar ParameterDispatchTraceInternals

theorem namedParameterCore_trace_success_sound :
    ParserTraceSuccessSound namedParameterCore NamedParameterCoreTraceParses := by
  intro input output value result
  by_cases guard : comptimeGuard input = true
  · have present := comptimeGuard_true_iff.mp guard
    rw [namedParameterCore_eq_comptime_of_prefix present] at result
    rcases comptimeNamedParameter_trace_success_sound result with ⟨trace, parsed, events⟩
    exact ⟨trace, .comptime present parsed, events⟩
  · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
    rw [namedParameterCore_eq_ordinary_of_prefix_absent absent] at result
    rcases ordinaryNamedParameter_trace_success_sound result with ⟨trace, parsed, events⟩
    exact ⟨trace, .ordinary absent parsed, events⟩

theorem namedParameterCore_reject_trace_sound :
    ParserTraceRejectSound namedParameterCore NamedParameterCoreTraceRejects := by
  intro input rejected failure result
  by_cases guard : comptimeGuard input = true
  · have present := comptimeGuard_true_iff.mp guard
    rw [namedParameterCore_eq_comptime_of_prefix present] at result
    rcases comptimeNamedParameter_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact ⟨trace, .comptime present rejection, events⟩
  · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
    rw [namedParameterCore_eq_ordinary_of_prefix_absent absent] at result
    rcases ordinaryNamedParameter_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact ⟨trace, .ordinary absent rejection, events⟩

theorem namedParameterCore_trace_success_complete :
    ParserTraceSuccessComplete namedParameterCore NamedParameterCoreTraceParses := by
  intro input value after trace parsed
  cases parsed with
  | ordinary absent raw =>
      rw [namedParameterCore_eq_ordinary_of_prefix_absent absent]
      exact ordinaryNamedParameter_trace_success_complete raw
  | comptime present raw =>
      rw [namedParameterCore_eq_comptime_of_prefix present]
      exact comptimeNamedParameter_trace_success_complete raw

theorem namedParameterCore_trace_reject_complete :
    ParserTraceRejectComplete namedParameterCore NamedParameterCoreTraceRejects := by
  intro input after report trace rejection
  cases rejection with
  | ordinary absent raw =>
      rw [namedParameterCore_eq_ordinary_of_prefix_absent absent]
      exact ordinaryNamedParameter_trace_reject_complete raw
  | comptime present raw =>
      rw [namedParameterCore_eq_comptime_of_prefix present]
      exact comptimeNamedParameter_trace_reject_complete raw

theorem namedParameterCore_success_context : ParserSuccessContext namedParameterCore := by
  intro input output value result
  have window := namedParameterCore_preservesTokenWindow input
  rw [result] at window
  exact ⟨namedParameterCore_preservesFile.file_eq_of_ok result, window.2⟩

theorem namedParameterCore_reject_context {input rejected : State} {failure : Failure}
    (result : namedParameterCore input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := namedParameterCore_preservesTokenWindow input
  rw [result] at window
  exact ⟨namedParameterCore_preservesFile.file_eq_of_reject result, window.2⟩

theorem namedParameterCore_trace_success_state_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterCoreTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      namedParameterCore input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    cases parsed with
    | ordinary absent raw =>
        rw [namedParameterCore_eq_ordinary_of_prefix_absent absent]
        exact ordinaryNamedParameter_trace_success_state_iff.mp raw
    | comptime present raw =>
        rw [namedParameterCore_eq_comptime_of_prefix present]
        exact comptimeNamedParameter_trace_success_state_iff.mp raw
  · intro result
    by_cases guard : comptimeGuard input = true
    · have present := comptimeGuard_true_iff.mp guard
      rw [namedParameterCore_eq_comptime_of_prefix present] at result
      exact .comptime present (comptimeNamedParameter_trace_success_state_iff.mpr result)
    · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
      rw [namedParameterCore_eq_ordinary_of_prefix_absent absent] at result
      exact .ordinary absent (ordinaryNamedParameter_trace_success_state_iff.mpr result)

theorem namedParameterCore_trace_reject_failure_state_iff
    {input : State} {failure : Failure} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔ namedParameterCore input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    cases rejection with
    | ordinary absent raw =>
        rw [namedParameterCore_eq_ordinary_of_prefix_absent absent]
        exact ordinaryNamedParameter_trace_reject_failure_state_iff.mp raw
    | comptime present raw =>
        rw [namedParameterCore_eq_comptime_of_prefix present]
        exact comptimeNamedParameter_trace_reject_failure_state_iff.mp raw
  · intro result
    by_cases guard : comptimeGuard input = true
    · have present := comptimeGuard_true_iff.mp guard
      rw [namedParameterCore_eq_comptime_of_prefix present] at result
      exact .comptime present (comptimeNamedParameter_trace_reject_failure_state_iff.mpr result)
    · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
      rw [namedParameterCore_eq_ordinary_of_prefix_absent absent] at result
      exact .ordinary absent (ordinaryNamedParameter_trace_reject_failure_state_iff.mpr result)

theorem namedParameterCore_trace_reject_state_iff
    {input : State} {report : ParseDiagnostic} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, namedParameterCore input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases namedParameterCore_trace_reject_complete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, namedParameterCore_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ namedParameterCore_trace_reject_failure_state_iff.mpr result

theorem namedParameterCore_ordinary_unrestricted : Parser.Ordinary namedParameterCore := by
  intro input
  by_cases guard : comptimeGuard input = true
  · rw [namedParameterCore_eq_comptime_of_prefix (comptimeGuard_true_iff.mp guard)]
    exact comptimeNamedParameter_ordinary input
  · rw [namedParameterCore_eq_ordinary_of_prefix_absent
      (comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard))]
    exact ordinaryNamedParameter_ordinary input

theorem namedParameterCore_ne_invariant_unrestricted (input : State) (error : ParserInvariantError) :
    namedParameterCore input ≠ .invariant error := by
  intro failed
  rcases namedParameterCore_ordinary_unrestricted input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.FunctionParameterInternals
