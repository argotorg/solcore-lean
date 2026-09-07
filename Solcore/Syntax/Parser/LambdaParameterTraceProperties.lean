import Solcore.Syntax.DeclarativeLambdaParameterTraceProperties
import Solcore.Syntax.Parser.LambdaParameterCoreTraceProperties
import Solcore.Syntax.Parser.LambdaParameterRecoveryTraceProperties
import Solcore.Syntax.Parser.FunctionParameterBoundaryOutcomeSoundnessProperties

/-! Public lambda parameters retain failed-core events when rewinding the cursor.
Only the non-boundary path commits the core report before standalone recovery.
Ordinary execution is unrestricted and supplies completeness independently of
the declarative uniqueness/disjointness specification. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar LambdaParameterInternals

theorem lambdaParameter_trace_success_sound :
    ParserTraceSuccessSound lambdaParameter LambdaParameterTraceParses := by
  intro input output value result
  cases coreResult : lambdaParameterCore input with
  | ok parameter next =>
      simp only [lambdaParameter, coreResult] at result
      cases result
      rcases lambdaParameterCore_trace_success_sound coreResult with ⟨trace, parsed, events⟩
      exact ⟨trace, .core parsed, events⟩
  | reject original failed =>
      let rewound := { failed with cursor := input.cursor }
      rcases lambdaParameterCore_reject_trace_sound coreResult with ⟨coreTrace, coreRejected, coreEvents⟩
      have frame := lambdaParameterCore_reject_context coreResult
      simp only [lambdaParameter, coreResult] at result
      change (if rewound.atEnd || isSymbol rewound .comma || isSymbol rewound .rightParen then
        .reject original rewound else recoverLambdaParameter (rewound.emit original.toDiagnostic)) = .ok value output at result
      split at result
      · contradiction
      · rename_i continues
        rcases recoverLambdaParameter_trace_success_sound result with ⟨trace, parsed, events⟩
        have recovery : LambdaParameterRecoveryTraceParses input.file.id input.window.endByte
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
  | invariant error => simp only [lambdaParameter, coreResult] at result; contradiction

theorem lambdaParameter_reject_trace_sound :
    ParserTraceRejectSound lambdaParameter LambdaParameterTraceRejects := by
  intro input rejected failure result
  cases coreResult : lambdaParameterCore input with
  | ok value next => simp only [lambdaParameter, coreResult] at result; contradiction
  | reject original failed =>
      let rewound := { failed with cursor := input.cursor }
      rcases lambdaParameterCore_reject_trace_sound coreResult with ⟨coreTrace, coreRejected, coreEvents⟩
      have frame := lambdaParameterCore_reject_context coreResult
      simp only [lambdaParameter, coreResult] at result
      change (if rewound.atEnd || isSymbol rewound .comma || isSymbol rewound .rightParen then
        .reject original rewound else recoverLambdaParameter (rewound.emit original.toDiagnostic)) =
          .reject failure rejected at result
      split at result
      · rename_i stops
        rcases Reply.reject.inj result with ⟨rfl, stateEq⟩
        rw [← stateEq]
        exact ⟨coreTrace, .boundary coreRejected
          (functionParameterBoundaryStops_of_guard_eq_true rewound stops), coreEvents⟩
      · rename_i continues
        rcases recoverLambdaParameter_reject_trace_sound result with ⟨trace, rejection, events⟩
        have recovery : LambdaParameterRecoveryTraceRejects input.file.id input.window.endByte
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
  | invariant error => simp only [lambdaParameter, coreResult] at result; contradiction

theorem lambdaParameter_preservesFile : Parser.PreservesFile lambdaParameter := by
  intro input
  cases coreResult : lambdaParameterCore input with
  | ok value next =>
      simp only [lambdaParameter, coreResult]
      exact lambdaParameterCore_preservesFile.file_eq_of_ok coreResult
  | reject failure failed =>
      have frame := lambdaParameterCore_preservesFile.file_eq_of_reject coreResult
      simp only [lambdaParameter, coreResult]
      split
      · exact frame
      · exact (recoverLambdaParameter_preservesFile _).trans frame
  | invariant error => simp only [lambdaParameter, coreResult]; trivial

theorem lambdaParameter_success_context : ParserSuccessContext lambdaParameter := by
  intro input output value result
  have window := lambdaParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨lambdaParameter_preservesFile.file_eq_of_ok result, window.2⟩

theorem lambdaParameter_reject_context {input rejected : State} {failure : Failure}
    (result : lambdaParameter input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := lambdaParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨lambdaParameter_preservesFile.file_eq_of_reject result, window.2⟩

theorem lambdaParameter_ordinary_unrestricted : Parser.Ordinary lambdaParameter := by
  intro input
  rcases lambdaParameterCore_ordinary_unrestricted input with
    ⟨value, next, parsed⟩ | ⟨failure, failed, rejected⟩
  · exact .inl ⟨value, next, by simp only [lambdaParameter, parsed]⟩
  · simp only [lambdaParameter, rejected]
    split
    · exact .inr ⟨_, _, rfl⟩
    · exact recoverLambdaParameter_ordinary _

theorem lambdaParameter_ne_invariant_unrestricted (input : State) (error : ParserInvariantError) :
    lambdaParameter input ≠ .invariant error := by
  intro failed
  rcases lambdaParameter_ordinary_unrestricted input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

theorem lambdaParameter_trace_success_complete :
    ParserTraceSuccessComplete lambdaParameter LambdaParameterTraceParses :=
  trace_success_complete_of_sound lambdaParameter_trace_success_sound lambdaParameter_reject_trace_sound
    (fun _ _ => lambdaParameterTraceExactOutcomeSpec) lambdaParameter_ne_invariant_unrestricted

theorem lambdaParameter_trace_reject_complete :
    ParserTraceRejectComplete lambdaParameter LambdaParameterTraceRejects :=
  trace_reject_complete_of_sound lambdaParameter_trace_success_sound lambdaParameter_reject_trace_sound
    (fun _ _ => lambdaParameterTraceExactOutcomeSpec) lambdaParameter_ne_invariant_unrestricted

end Solcore.Syntax.Parser
