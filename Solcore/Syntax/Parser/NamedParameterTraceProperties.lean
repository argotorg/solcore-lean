import Solcore.Syntax.DeclarativeNamedParameterTraceProperties
import Solcore.Syntax.Parser.NamedParameterCoreTraceProperties
import Solcore.Syntax.Parser.ParameterRecoveryTraceProperties
import Solcore.Syntax.Parser.FunctionParameterBoundaryOutcomeSoundnessProperties

/-! Public named parameters retain failed-core events when rewinding the cursor.
Only the non-boundary path commits the core report before standalone recovery.
Ordinary execution is unrestricted and supplies completeness independently of
the declarative uniqueness/disjointness specification. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar FunctionParameterInternals

theorem namedParameter_trace_success_sound :
    ParserTraceSuccessSound namedParameter NamedParameterTraceParses := by
  intro input output value result
  cases coreResult : namedParameterCore input with
  | ok parameter next =>
      simp only [namedParameter, coreResult] at result
      cases result
      rcases namedParameterCore_trace_success_sound coreResult with ⟨trace, parsed, events⟩
      exact ⟨trace, .core parsed, events⟩
  | reject original failed =>
      let rewound := { failed with cursor := input.cursor }
      rcases namedParameterCore_reject_trace_sound coreResult with ⟨coreTrace, coreRejected, coreEvents⟩
      have frame := namedParameterCore_reject_context coreResult
      simp only [namedParameter, coreResult] at result
      change (if rewound.atEnd || isSymbol rewound .comma || isSymbol rewound .rightParen then
        .reject original rewound else recoverParameter (rewound.emit original.toDiagnostic)) = .ok value output at result
      split at result
      · contradiction
      · rename_i continues
        rcases recoverParameter_trace_success_sound result with ⟨trace, parsed, events⟩
        have recovery : FunctionParameterRecoveryTraceParses input.file.id input.window.endByte
            (parameterTraceRewind input.declarativeRemainder failed.declarativeRemainder)
            value output.declarativeRemainder trace := by
          simpa only [State.emit, rewound, State.declarativeRemainder, parameterTraceRewind,
            frame.1, frame.2] using parsed
        refine ⟨(coreTrace ++ [original.toDiagnostic]) ++ trace,
          .recovered coreRejected
            (no_functionParameterBoundaryStops_of_guard_eq_false rewound (Bool.eq_false_iff.mpr continues)) recovery, ?_⟩
        calc
          output.diagnostics = (failed.diagnostics ++ [original.toDiagnostic]) ++ trace := by
            simpa only [State.emit, rewound, State.diagnostics, List.reverse_cons] using events
          _ = input.diagnostics ++ ((coreTrace ++ [original.toDiagnostic]) ++ trace) := by
            rw [coreEvents]
            simp only [List.append_assoc]
  | invariant error => simp only [namedParameter, coreResult] at result; contradiction

theorem namedParameter_reject_trace_sound :
    ParserTraceRejectSound namedParameter NamedParameterTraceRejects := by
  intro input rejected failure result
  cases coreResult : namedParameterCore input with
  | ok value next => simp only [namedParameter, coreResult] at result; contradiction
  | reject original failed =>
      let rewound := { failed with cursor := input.cursor }
      rcases namedParameterCore_reject_trace_sound coreResult with ⟨coreTrace, coreRejected, coreEvents⟩
      have frame := namedParameterCore_reject_context coreResult
      simp only [namedParameter, coreResult] at result
      change (if rewound.atEnd || isSymbol rewound .comma || isSymbol rewound .rightParen then
        .reject original rewound else recoverParameter (rewound.emit original.toDiagnostic)) =
          .reject failure rejected at result
      split at result
      · rename_i stops
        rcases Reply.reject.inj result with ⟨rfl, stateEq⟩
        rw [← stateEq]
        exact ⟨coreTrace, .boundary coreRejected
          (functionParameterBoundaryStops_of_guard_eq_true rewound stops), coreEvents⟩
      · rename_i continues
        rcases recoverParameter_reject_trace_sound result with ⟨trace, rejection, events⟩
        have recovery : FunctionParameterRecoveryTraceRejects input.file.id input.window.endByte
            (parameterTraceRewind input.declarativeRemainder failed.declarativeRemainder)
            rejected.declarativeRemainder failure.toDiagnostic trace := by
          simpa only [State.emit, rewound, State.declarativeRemainder, parameterTraceRewind,
            frame.1, frame.2] using rejection
        refine ⟨(coreTrace ++ [original.toDiagnostic]) ++ trace,
          .recovery coreRejected
            (no_functionParameterBoundaryStops_of_guard_eq_false rewound (Bool.eq_false_iff.mpr continues)) recovery, ?_⟩
        calc
          rejected.diagnostics = (failed.diagnostics ++ [original.toDiagnostic]) ++ trace := by
            simpa only [State.emit, rewound, State.diagnostics, List.reverse_cons] using events
          _ = input.diagnostics ++ ((coreTrace ++ [original.toDiagnostic]) ++ trace) := by
            rw [coreEvents]
            simp only [List.append_assoc]
  | invariant error => simp only [namedParameter, coreResult] at result; contradiction

theorem namedParameter_preservesFile : Parser.PreservesFile namedParameter := by
  intro input
  cases coreResult : namedParameterCore input with
  | ok value next =>
      simp only [namedParameter, coreResult]
      exact namedParameterCore_preservesFile.file_eq_of_ok coreResult
  | reject failure failed =>
      have frame := namedParameterCore_preservesFile.file_eq_of_reject coreResult
      simp only [namedParameter, coreResult]
      split
      · exact frame
      · exact (recoverParameter_preservesFile _).trans frame
  | invariant error => simp only [namedParameter, coreResult]; trivial

theorem namedParameter_success_context : ParserSuccessContext namedParameter := by
  intro input output value result
  have window := namedParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨namedParameter_preservesFile.file_eq_of_ok result, window.2⟩

theorem namedParameter_reject_context {input rejected : State} {failure : Failure}
    (result : namedParameter input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := namedParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨namedParameter_preservesFile.file_eq_of_reject result, window.2⟩

theorem namedParameter_ordinary_unrestricted : Parser.Ordinary namedParameter := by
  intro input
  rcases namedParameterCore_ordinary_unrestricted input with
    ⟨value, next, parsed⟩ | ⟨failure, failed, rejected⟩
  · exact .inl ⟨value, next, by simp only [namedParameter, parsed]⟩
  · simp only [namedParameter, rejected]
    split
    · exact .inr ⟨_, _, rfl⟩
    · exact recoverParameter_ordinary _

theorem namedParameter_ne_invariant_unrestricted (input : State) (error : ParserInvariantError) :
    namedParameter input ≠ .invariant error := by
  intro failed
  rcases namedParameter_ordinary_unrestricted input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

theorem namedParameter_trace_success_complete :
    ParserTraceSuccessComplete namedParameter NamedParameterTraceParses :=
  trace_success_complete_of_sound namedParameter_trace_success_sound namedParameter_reject_trace_sound
    (fun _ _ => namedParameterTraceExactOutcomeSpec) namedParameter_ne_invariant_unrestricted

theorem namedParameter_trace_reject_complete :
    ParserTraceRejectComplete namedParameter NamedParameterTraceRejects :=
  trace_reject_complete_of_sound namedParameter_trace_success_sound namedParameter_reject_trace_sound
    (fun _ _ => namedParameterTraceExactOutcomeSpec) namedParameter_ne_invariant_unrestricted

end Solcore.Syntax.Parser
