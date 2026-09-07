import Solcore.Syntax.DeclarativeLambdaParameterRawRejectionTraceProperties
import Solcore.Syntax.Parser.ParameterNameFinishingTraceProperties
import Solcore.Syntax.Parser.LambdaParameterTailTraceStateProperties
import Solcore.Syntax.Parser.DiagnosticTraceCompletenessFromSoundnessProperties

/-! Raw ordinary lambda parameters check the identifier spelling before entering
the tail. All prior events and the complete first failure are retained, without
the selected-core guard or the public parameter recovery policy. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar

theorem ordinaryLambdaParameter_eq_of_checkedName
    {input : State} {name : Identifier} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : CheckedParameterNameTraceParses input.declarativeRemainder name after trace) :
    ordinaryLambdaParameter input =
      ordinaryLambdaParameterTail name (input.traceResult after trace) := by
  exact checkedParameterName_continue_of_trace
    (fun name => ordinaryLambdaParameterTail name) parsed

theorem ordinaryLambdaParameter_trace_success_sound :
    ParserTraceSuccessSound ordinaryLambdaParameter OrdinaryLambdaParameterTraceParses := by
  intro input output value result
  cases nameResult : identifier .parameter input with
  | invariant error => simp [ordinaryLambdaParameter, bind, nameResult] at result
  | reject failure rejected => simp [ordinaryLambdaParameter, bind, nameResult] at result
  | ok name next =>
      rcases identifier_success_trace_sound .parameter nameResult with ⟨nameEvents, identifier, _⟩
      rcases parameterNameFinishingTrace_exists name with ⟨finishEvents, finished⟩
      have headParsed := CheckedParameterNameTraceParses.parsed identifier finished
      rw [ordinaryLambdaParameter_eq_of_checkedName headParsed] at result
      rcases ordinaryLambdaParameterTail_trace_success_sound name result with
        ⟨tailEvents, parsed, events⟩
      exact ⟨_, .parsed headParsed parsed, by
        simpa only [State.traceResult_diagnostics, List.append_assoc] using events⟩

theorem ordinaryLambdaParameter_reject_trace_sound :
    ParserTraceRejectSound ordinaryLambdaParameter OrdinaryLambdaParameterTraceRejects := by
  intro input rejected failure result
  cases nameResult : identifier .parameter input with
  | invariant error => simp [ordinaryLambdaParameter, bind, nameResult] at result
  | reject actual next =>
      simp only [ordinaryLambdaParameter, bind, nameResult] at result
      cases result
      have same := identifier_reject_state_eq .parameter nameResult
      subst rejected
      have reported := (identifier_reject_reports_iff .parameter).mpr ⟨failure, nameResult, rfl⟩
      exact ⟨[], .nameRejected reported.1 reported.2, by simp⟩
  | ok name next =>
      rcases identifier_success_trace_sound .parameter nameResult with ⟨nameEvents, identifier, _⟩
      rcases parameterNameFinishingTrace_exists name with ⟨finishEvents, finished⟩
      have headParsed := CheckedParameterNameTraceParses.parsed identifier finished
      rw [ordinaryLambdaParameter_eq_of_checkedName headParsed] at result
      rcases ordinaryLambdaParameterTail_reject_trace_sound name result with
        ⟨tailEvents, rejection, events⟩
      exact ⟨_, .tailRejected headParsed rejection, by
        simpa only [State.traceResult_diagnostics, List.append_assoc] using events⟩

theorem ordinaryLambdaParameter_ordinary : Parser.Ordinary ordinaryLambdaParameter := by
  intro input
  rcases identifier_ordinary .parameter input with ⟨name, next, result⟩ | ⟨failure, rejected, result⟩
  · rcases identifier_success_trace_sound .parameter result with ⟨nameEvents, identifier, _⟩
    rcases parameterNameFinishingTrace_exists name with ⟨finishEvents, finished⟩
    have headParsed := CheckedParameterNameTraceParses.parsed identifier finished
    rw [ordinaryLambdaParameter_eq_of_checkedName headParsed]
    exact ordinaryLambdaParameterTail_ordinary name _
  · exact .inr ⟨failure, rejected, by simp only [ordinaryLambdaParameter, bind, result]⟩

theorem ordinaryLambdaParameter_ne_invariant (input : State) (error : ParserInvariantError) :
    ordinaryLambdaParameter input ≠ .invariant error := by
  intro failed
  rcases ordinaryLambdaParameter_ordinary input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

theorem ordinaryLambdaParameter_trace_success_complete :
    ParserTraceSuccessComplete ordinaryLambdaParameter OrdinaryLambdaParameterTraceParses :=
  trace_success_complete_of_sound ordinaryLambdaParameter_trace_success_sound
    ordinaryLambdaParameter_reject_trace_sound (fun _ _ => ordinaryLambdaParameterTraceExactOutcomeSpec)
    ordinaryLambdaParameter_ne_invariant

theorem ordinaryLambdaParameter_trace_reject_complete :
    ParserTraceRejectComplete ordinaryLambdaParameter OrdinaryLambdaParameterTraceRejects :=
  trace_reject_complete_of_sound ordinaryLambdaParameter_trace_success_sound
    ordinaryLambdaParameter_reject_trace_sound (fun _ _ => ordinaryLambdaParameterTraceExactOutcomeSpec)
    ordinaryLambdaParameter_ne_invariant

theorem ordinaryLambdaParameter_success_context : ParserSuccessContext ordinaryLambdaParameter := by
  intro input output value result
  have window := ordinaryLambdaParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨ordinaryLambdaParameter_preservesFile.file_eq_of_ok result, window.2⟩

theorem ordinaryLambdaParameter_reject_context {input rejected : State} {failure : Failure}
    (result : ordinaryLambdaParameter input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := ordinaryLambdaParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨ordinaryLambdaParameter_preservesFile.file_eq_of_reject result, window.2⟩

end Solcore.Syntax.Parser.LambdaParameterInternals
