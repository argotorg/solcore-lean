import Solcore.Syntax.DeclarativeNamedParameterRawRejectionTraceProperties
import Solcore.Syntax.Parser.ParameterNameFinishingTraceProperties
import Solcore.Syntax.Parser.ParameterSourceFrameProperties
import Solcore.Syntax.Parser.DiagnosticTraceCompletenessFromSoundnessProperties

/-! Raw ordinary named parameters check the identifier spelling before entering
the tail. All prior events and the complete first failure are retained, without
the selected-core guard or the public parameter recovery policy. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

theorem ordinaryNamedParameter_eq_of_checkedName
    {input : State} {name : Identifier} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : CheckedParameterNameTraceParses input.declarativeRemainder name after trace) :
    ordinaryNamedParameter input =
      namedParameterTail name.span none name name.span (input.traceResult after trace) := by
  exact checkedParameterName_continue_of_trace
    (fun name => namedParameterTail name.span none name name.span) parsed

theorem ordinaryNamedParameter_trace_success_sound :
    ParserTraceSuccessSound ordinaryNamedParameter OrdinaryNamedParameterTraceParses := by
  intro input output value result
  cases nameResult : identifier .parameter input with
  | invariant error => simp [ordinaryNamedParameter, bind, nameResult] at result
  | reject failure rejected => simp [ordinaryNamedParameter, bind, nameResult] at result
  | ok name next =>
      rcases identifier_success_trace_sound .parameter nameResult with ⟨nameEvents, identifier, _⟩
      rcases parameterNameFinishingTrace_exists name with ⟨finishEvents, finished⟩
      have headParsed := CheckedParameterNameTraceParses.parsed identifier finished
      rw [ordinaryNamedParameter_eq_of_checkedName headParsed] at result
      rcases namedParameterTail_trace_success_sound name.span none name name.span result with
        ⟨tailEvents, parsed, events⟩
      exact ⟨_, .parsed headParsed parsed, by
        simpa only [State.traceResult_diagnostics, List.append_assoc] using events⟩

theorem ordinaryNamedParameter_reject_trace_sound :
    ParserTraceRejectSound ordinaryNamedParameter OrdinaryNamedParameterTraceRejects := by
  intro input rejected failure result
  cases nameResult : identifier .parameter input with
  | invariant error => simp [ordinaryNamedParameter, bind, nameResult] at result
  | reject actual next =>
      simp only [ordinaryNamedParameter, bind, nameResult] at result
      cases result
      have same := identifier_reject_state_eq .parameter nameResult
      subst rejected
      have reported := (identifier_reject_reports_iff .parameter).mpr ⟨failure, nameResult, rfl⟩
      exact ⟨[], .nameRejected reported.1 reported.2, by simp⟩
  | ok name next =>
      rcases identifier_success_trace_sound .parameter nameResult with ⟨nameEvents, identifier, _⟩
      rcases parameterNameFinishingTrace_exists name with ⟨finishEvents, finished⟩
      have headParsed := CheckedParameterNameTraceParses.parsed identifier finished
      rw [ordinaryNamedParameter_eq_of_checkedName headParsed] at result
      rcases namedParameterTail_reject_trace_sound name.span none name name.span result with
        ⟨tailEvents, rejection, events⟩
      exact ⟨_, .tailRejected headParsed rejection, by
        simpa only [State.traceResult_diagnostics, List.append_assoc] using events⟩

theorem ordinaryNamedParameter_ordinary : Parser.Ordinary ordinaryNamedParameter := by
  intro input
  rcases identifier_ordinary .parameter input with ⟨name, next, result⟩ | ⟨failure, rejected, result⟩
  · rcases identifier_success_trace_sound .parameter result with ⟨nameEvents, identifier, _⟩
    rcases parameterNameFinishingTrace_exists name with ⟨finishEvents, finished⟩
    have headParsed := CheckedParameterNameTraceParses.parsed identifier finished
    rw [ordinaryNamedParameter_eq_of_checkedName headParsed]
    exact namedParameterTail_ordinary name.span none name name.span _
  · exact .inr ⟨failure, rejected, by simp only [ordinaryNamedParameter, bind, result]⟩

theorem ordinaryNamedParameter_ne_invariant (input : State) (error : ParserInvariantError) :
    ordinaryNamedParameter input ≠ .invariant error := by
  intro failed
  rcases ordinaryNamedParameter_ordinary input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

theorem ordinaryNamedParameter_trace_success_complete :
    ParserTraceSuccessComplete ordinaryNamedParameter OrdinaryNamedParameterTraceParses :=
  trace_success_complete_of_sound ordinaryNamedParameter_trace_success_sound
    ordinaryNamedParameter_reject_trace_sound (fun _ _ => ordinaryNamedParameterTraceExactOutcomeSpec)
    ordinaryNamedParameter_ne_invariant

theorem ordinaryNamedParameter_trace_reject_complete :
    ParserTraceRejectComplete ordinaryNamedParameter OrdinaryNamedParameterTraceRejects :=
  trace_reject_complete_of_sound ordinaryNamedParameter_trace_success_sound
    ordinaryNamedParameter_reject_trace_sound (fun _ _ => ordinaryNamedParameterTraceExactOutcomeSpec)
    ordinaryNamedParameter_ne_invariant

theorem ordinaryNamedParameter_success_context : ParserSuccessContext ordinaryNamedParameter := by
  intro input output value result
  have window := ordinaryNamedParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨ordinaryNamedParameter_preservesFile.file_eq_of_ok result, window.2⟩

theorem ordinaryNamedParameter_reject_context {input rejected : State} {failure : Failure}
    (result : ordinaryNamedParameter input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := ordinaryNamedParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨ordinaryNamedParameter_preservesFile.file_eq_of_reject result, window.2⟩

end Solcore.Syntax.Parser.FunctionParameterInternals
