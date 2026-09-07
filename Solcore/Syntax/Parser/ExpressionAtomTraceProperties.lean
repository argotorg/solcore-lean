import Solcore.Syntax.DeclarativeExpressionAtomTraceGrammar
import Solcore.Syntax.Parser.ExpressionAtomTraceContextProperties

/-! Public atom trace contracts over the actual core. The rejected source and
end byte are explicit; tokens and end index may change and survive rewind.
Completeness composes only matching core completeness contracts and standalone
recovery, without ordinary-execution, progress, or validity assumptions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}
  {coreTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {coreRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionAtom_trace_success_sound
    (coreSuccessSound : ParserTraceSuccessSound (expressionAtomCore nested block) coreTrace)
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceSuccessSound (expressionAtom nested block) (ExpressionAtomTraceParses coreTrace coreRejects) := by
  intro input output value result
  cases coreResult : expressionAtomCore nested block input with
  | ok parameter next =>
      simp only [expressionAtom, coreResult] at result
      cases result
      rcases coreSuccessSound coreResult with ⟨trace, parsed, events⟩
      exact ⟨trace, .core parsed, events⟩
  | reject original failed =>
      let rewound := { failed with cursor := input.cursor }
      rcases coreRejectSound coreResult with ⟨coreTrace, coreRejected, coreEvents⟩
      have frame := coreRejectFrame coreResult
      simp only [expressionAtom, coreResult] at result
      change (if isAtomBoundary rewound then
        .reject original rewound else recoverAtom (rewound.emit original.toDiagnostic)) = .ok value output at result
      split at result
      · contradiction
      · rename_i continues
        rcases recoverAtom_trace_success_sound result with ⟨trace, parsed, events⟩
        have recovery : ExpressionAtomRecoveryTraceParses input.file.id input.window.endByte
            (expressionAtomTraceRewind input.declarativeRemainder failed.declarativeRemainder)
            value output.declarativeRemainder trace := by
          simpa only [State.emit, rewound, State.declarativeRemainder, expressionAtomTraceRewind,
            frame.1, frame.2] using parsed
        refine ⟨(coreTrace ++ [original.toDiagnostic]) ++ trace,
          .recovered coreRejected
            (no_expressionAtomBoundaryStops_of_isAtomBoundary_eq_false rewound (Bool.eq_false_iff.mpr continues)) recovery, ?_⟩
        calc
          output.diagnostics = (failed.diagnostics ++ [original.toDiagnostic]) ++ trace := by
            simpa only [State.emit, rewound, State.diagnostics, List.reverse_cons] using events
          _ = input.diagnostics ++ ((coreTrace ++ [original.toDiagnostic]) ++ trace) := by
            rw [coreEvents]
            simp only [List.append_assoc]
  | invariant error => simp only [expressionAtom, coreResult] at result; contradiction

theorem expressionAtom_reject_trace_sound
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceRejectSound (expressionAtom nested block) (ExpressionAtomTraceRejects coreRejects) := by
  intro input rejected failure result
  cases coreResult : expressionAtomCore nested block input with
  | ok value next => simp only [expressionAtom, coreResult] at result; contradiction
  | reject original failed =>
      let rewound := { failed with cursor := input.cursor }
      rcases coreRejectSound coreResult with ⟨coreTrace, coreRejected, coreEvents⟩
      have frame := coreRejectFrame coreResult
      simp only [expressionAtom, coreResult] at result
      change (if isAtomBoundary rewound then
        .reject original rewound else recoverAtom (rewound.emit original.toDiagnostic)) =
          .reject failure rejected at result
      split at result
      · rename_i stops
        rcases Reply.reject.inj result with ⟨rfl, stateEq⟩
        rw [← stateEq]
        exact ⟨coreTrace, .boundary coreRejected
          (expressionAtomBoundaryStops_of_isAtomBoundary rewound stops), coreEvents⟩
      · rename_i continues
        rcases recoverAtom_reject_trace_sound result with ⟨trace, rejection, events⟩
        have recovery : ExpressionAtomRecoveryTraceRejects input.file.id input.window.endByte
            (expressionAtomTraceRewind input.declarativeRemainder failed.declarativeRemainder)
            rejected.declarativeRemainder failure.toDiagnostic trace := by
          simpa only [State.emit, rewound, State.declarativeRemainder, expressionAtomTraceRewind,
            frame.1, frame.2] using rejection
        refine ⟨(coreTrace ++ [original.toDiagnostic]) ++ trace,
          .recovery coreRejected
            (no_expressionAtomBoundaryStops_of_isAtomBoundary_eq_false rewound (Bool.eq_false_iff.mpr continues)) recovery, ?_⟩
        calc
          rejected.diagnostics = (failed.diagnostics ++ [original.toDiagnostic]) ++ trace := by
            simpa only [State.emit, rewound, State.diagnostics, List.reverse_cons] using events
          _ = input.diagnostics ++ ((coreTrace ++ [original.toDiagnostic]) ++ trace) := by
            rw [coreEvents]
            simp only [List.append_assoc]
  | invariant error => simp only [expressionAtom, coreResult] at result; contradiction

theorem expressionAtom_trace_success_complete
    (coreSuccessComplete : ParserTraceSuccessComplete (expressionAtomCore nested block) coreTrace)
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceSuccessComplete (expressionAtom nested block) (ExpressionAtomTraceParses coreTrace coreRejects) := by
  intro input value after trace parsed
  cases parsed with
  | core parsed =>
      rcases coreSuccessComplete parsed with ⟨output, result, afterEq, events⟩
      exact ⟨output, by simp only [expressionAtom, result], afterEq, events⟩
  | recovered coreRejected continues recovered =>
      rename_i failedR coreReport coreTraceEvents recoveryTrace
      rcases coreRejectComplete coreRejected with ⟨original, failed, coreResult, failedEq, reportEq, coreEvents⟩
      have frame := coreRejectFrame coreResult
      let rewound : State := { failed with cursor := input.cursor }
      have rewindEq : rewound.declarativeRemainder = _ :=
        congrArg (expressionAtomTraceRewind input.declarativeRemainder) failedEq
      rw [← rewindEq] at continues
      have guard := (isAtomBoundary_false_iff rewound).mpr continues
      dsimp only [rewound] at guard
      have ownerEq : (rewound.emit original.toDiagnostic).file.id = input.file.id := congrArg (·.id) frame.1
      have endEq : (rewound.emit original.toDiagnostic).window.endByte = input.window.endByte := frame.2
      rw [← rewindEq, ← ownerEq, ← endEq] at recovered
      rcases recoverAtom_trace_success_complete (input := rewound.emit original.toDiagnostic) recovered with
        ⟨output, result, afterEq, events⟩
      refine ⟨output, by simpa only [expressionAtom, coreResult, guard, Bool.false_eq_true, if_false] using result,
        afterEq, ?_⟩
      have events' : output.diagnostics = (failed.diagnostics ++ [original.toDiagnostic]) ++ recoveryTrace := by
        simpa only [State.emit, rewound, State.diagnostics, List.reverse_cons] using events
      rw [events', coreEvents, reportEq]
      simp only [List.append_assoc]

theorem expressionAtom_trace_reject_complete
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceRejectComplete (expressionAtom nested block) (ExpressionAtomTraceRejects coreRejects) := by
  intro input after report trace rejection
  cases rejection with
  | boundary coreRejected stops =>
      rcases coreRejectComplete coreRejected with ⟨original, failed, coreResult, failedEq, reportEq, coreEvents⟩
      let rewound : State := { failed with cursor := input.cursor }
      have rewindEq : rewound.declarativeRemainder = _ :=
        congrArg (expressionAtomTraceRewind input.declarativeRemainder) failedEq
      rw [← rewindEq] at stops
      have guard := (isAtomBoundary_true_iff rewound).mpr stops
      dsimp only [rewound] at guard
      exact ⟨original, rewound, by simp only [expressionAtom, coreResult, guard, if_true]; rfl,
        rewindEq, reportEq, coreEvents⟩
  | recovery coreRejected continues recoveryRejected =>
      rename_i failedR coreReport coreTraceEvents recoveryTrace
      rcases coreRejectComplete coreRejected with ⟨original, failed, coreResult, failedEq, reportEq, coreEvents⟩
      have frame := coreRejectFrame coreResult
      let rewound : State := { failed with cursor := input.cursor }
      have rewindEq : rewound.declarativeRemainder = _ :=
        congrArg (expressionAtomTraceRewind input.declarativeRemainder) failedEq
      rw [← rewindEq] at continues
      have guard := (isAtomBoundary_false_iff rewound).mpr continues
      dsimp only [rewound] at guard
      have ownerEq : (rewound.emit original.toDiagnostic).file.id = input.file.id := congrArg (·.id) frame.1
      have endEq : (rewound.emit original.toDiagnostic).window.endByte = input.window.endByte := frame.2
      rw [← rewindEq, ← ownerEq, ← endEq] at recoveryRejected
      rcases recoverAtom_trace_reject_complete (input := rewound.emit original.toDiagnostic) recoveryRejected with
        ⟨failure, rejected, result, afterEq, finalReportEq, events⟩
      refine ⟨failure, rejected,
        by simpa only [expressionAtom, coreResult, guard, Bool.false_eq_true, if_false] using result,
        afterEq, finalReportEq, ?_⟩
      have events' : rejected.diagnostics = (failed.diagnostics ++ [original.toDiagnostic]) ++ recoveryTrace := by
        simpa only [State.emit, rewound, State.diagnostics, List.reverse_cons] using events
      rw [events', coreEvents, reportEq]
      simp only [List.append_assoc]

end Solcore.Syntax.Parser
