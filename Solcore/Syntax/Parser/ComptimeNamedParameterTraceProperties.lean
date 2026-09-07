import Solcore.Syntax.Parser.OrdinaryNamedParameterTraceProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties

/-! The raw comptime path has a silent contextual marker, a checked identifier,
and the named tail. The second name never receives the ordinary-name warning.
Marker, name, and tail failures are separate first-failure alternatives. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

theorem comptimeNamedParameter_trace_success_sound :
    ParserTraceSuccessSound comptimeNamedParameter ComptimeNamedParameterTraceParses := by
  intro input output value result
  unfold comptimeNamedParameter at result
  simp only [bind] at result
  cases markerResult : contextual .comptime .parameter input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      have markerParsed := contextual_success_exactTokenParses .comptime .parameter markerResult
      have markerState := (contextual_ok_tokenAt .comptime .parameter markerResult).2
      subst afterMarker
      simp only [markerResult] at result
      cases nameResult : identifier .parameter { input with cursor := input.cursor + 1 } with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name next =>
          simp only [nameResult] at result
          rcases identifier_success_trace_sound .parameter nameResult with ⟨nameEvents, nameParsed, nameEventsEq⟩
          have frame := identifier_success_context_eq .parameter nameResult
          rcases namedParameterTail_trace_success_sound marker.span (some marker.span) name
            (SourceSpan.cover marker.span name.span) result with ⟨tailEvents, tail, tailEventsEq⟩
          refine ⟨nameEvents ++ tailEvents, .parsed marker.span markerParsed nameParsed ?_, ?_⟩
          · simpa only [frame.1, frame.2] using tail
          · rw [tailEventsEq, nameEventsEq]
            exact List.append_assoc _ _ _

theorem comptimeNamedParameter_reject_trace_sound :
    ParserTraceRejectSound comptimeNamedParameter ComptimeNamedParameterTraceRejects := by
  intro input rejected failure result
  unfold comptimeNamedParameter at result
  simp only [bind] at result
  cases markerResult : contextual .comptime .parameter input with
  | invariant error => simp [markerResult] at result
  | reject actual next =>
      simp only [markerResult] at result
      cases result
      have same := acceptToken_reject_state_shape (.contextual .comptime) .parameter
        (·.isContextual .comptime) markerResult
      subst rejected
      have reported := (contextual_reject_reports_iff .comptime .parameter).mpr ⟨failure, markerResult, rfl⟩
      exact ⟨[], .markerMissing reported.1 reported.2, by simp⟩
  | ok marker afterMarker =>
      have markerParsed := contextual_success_exactTokenParses .comptime .parameter markerResult
      have markerState := (contextual_ok_tokenAt .comptime .parameter markerResult).2
      subst afterMarker
      simp only [markerResult] at result
      cases nameResult : identifier .parameter { input with cursor := input.cursor + 1 } with
      | invariant error => simp [nameResult] at result
      | reject actual next =>
          simp only [nameResult] at result
          cases result
          have same := identifier_reject_state_eq .parameter nameResult
          subst rejected
          have reported := (identifier_reject_reports_iff .parameter).mpr ⟨failure, nameResult, rfl⟩
          exact ⟨[], .nameRejected marker.span markerParsed reported.1 reported.2, by simp; rfl⟩
      | ok name next =>
          simp only [nameResult] at result
          rcases identifier_success_trace_sound .parameter nameResult with ⟨nameEvents, nameParsed, nameEventsEq⟩
          have frame := identifier_success_context_eq .parameter nameResult
          rcases namedParameterTail_reject_trace_sound marker.span (some marker.span) name
            (SourceSpan.cover marker.span name.span) result with ⟨tailEvents, tail, tailEventsEq⟩
          refine ⟨nameEvents ++ tailEvents, .tailRejected marker.span markerParsed nameParsed ?_, ?_⟩
          · simpa only [frame.1, frame.2] using tail
          · rw [tailEventsEq, nameEventsEq]
            exact List.append_assoc _ _ _

theorem comptimeNamedParameter_ordinary : Parser.Ordinary comptimeNamedParameter := by
  intro input
  rcases contextual_ordinary .comptime .parameter input with
    ⟨marker, afterMarker, markerResult⟩ | ⟨failure, rejected, markerResult⟩
  · rcases identifier_ordinary .parameter afterMarker with
      ⟨name, next, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · rcases namedParameterTail_ordinary marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span) next with
        ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
      · exact .inl ⟨value, output, by simp only [comptimeNamedParameter, bind, markerResult, nameResult, result]⟩
      · exact .inr ⟨failure, rejected, by simp only [comptimeNamedParameter, bind, markerResult, nameResult, result]⟩
    · exact .inr ⟨failure, rejected, by simp only [comptimeNamedParameter, bind, markerResult, nameResult]⟩
  · exact .inr ⟨failure, rejected, by simp only [comptimeNamedParameter, bind, markerResult]⟩

theorem comptimeNamedParameter_ne_invariant (input : State) (error : ParserInvariantError) :
    comptimeNamedParameter input ≠ .invariant error := by
  intro failed
  rcases comptimeNamedParameter_ordinary input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

theorem comptimeNamedParameter_trace_success_complete :
    ParserTraceSuccessComplete comptimeNamedParameter ComptimeNamedParameterTraceParses :=
  trace_success_complete_of_sound comptimeNamedParameter_trace_success_sound
    comptimeNamedParameter_reject_trace_sound (fun _ _ => comptimeNamedParameterTraceExactOutcomeSpec)
    comptimeNamedParameter_ne_invariant

theorem comptimeNamedParameter_trace_reject_complete :
    ParserTraceRejectComplete comptimeNamedParameter ComptimeNamedParameterTraceRejects :=
  trace_reject_complete_of_sound comptimeNamedParameter_trace_success_sound
    comptimeNamedParameter_reject_trace_sound (fun _ _ => comptimeNamedParameterTraceExactOutcomeSpec)
    comptimeNamedParameter_ne_invariant

theorem comptimeNamedParameter_success_context : ParserSuccessContext comptimeNamedParameter := by
  intro input output value result
  have window := comptimeNamedParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨comptimeNamedParameter_preservesFile.file_eq_of_ok result, window.2⟩

theorem comptimeNamedParameter_reject_context {input rejected : State} {failure : Failure}
    (result : comptimeNamedParameter input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := comptimeNamedParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨comptimeNamedParameter_preservesFile.file_eq_of_reject result, window.2⟩

end Solcore.Syntax.Parser.FunctionParameterInternals
