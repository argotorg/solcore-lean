import Solcore.Syntax.Parser.OptionalDotConstructorArgumentsRejectionTraceProperties

/-! Exact raw leading-dot rejection through the real Boolean-first name
parser and conditional child expression contracts. Dispatcher selection is not
assumed; the first dot/name/argument report and preceding events remain exact. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem dotConstructor_reject_trace_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceRejectSound (dotConstructor nested)
      (DeclarativeGrammar.DotConstructorTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  unfold dotConstructor at result
  cases dotResult : symbol .dot .expression input with
  | invariant error => simp [bind, dotResult] at result
  | reject dotFailure dotRejected =>
      have shape := symbol_reject_state_eq .dot .expression dotResult
      subst dotRejected
      simp only [bind, dotResult] at result
      cases result
      have reported := (symbol_reject_reports_iff .dot .expression).mpr ⟨failure, dotResult, rfl⟩
      exact ⟨[], .dotMissing reported.1 reported.2, by simp⟩
  | ok dot afterDot =>
      have dotParsed := symbol_success_exactTokenParses .dot .expression dotResult
      have dotShape := (symbol_ok_tokenAt .dot .expression dotResult).2
      simp only [bind, dotResult] at result
      cases nameResult : expressionName afterDot with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          have nameTrace := expressionName_reject_trace_sound nameResult
          refine ⟨[], .nameRejected dot.span dotParsed ?_, ?_⟩
          · simpa only [dotShape] using nameTrace.1
          · rw [nameTrace.2, dotShape]; simp only [State.diagnostics, List.append_nil]
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalDotConstructorArguments nested afterName with
          | invariant error => simp [argumentsResult] at result
          | ok arguments output => simp [argumentsResult, pure] at result
          | reject argumentsFailure argumentsRejected =>
              simp only [argumentsResult] at result
              cases result
              rcases expressionName_success_trace_sound nameResult with ⟨nameEvents, nameParsed, nameEq⟩
              have frame := expressionName_success_context_eq nameResult
              rcases optionalDotConstructorArguments_reject_trace_sound successSound rejectSound contextFrame
                  argumentsResult with ⟨argumentEvents, argumentsRejected, argumentsEq⟩
              refine ⟨nameEvents ++ argumentEvents, .argumentsRejected (name := name)
                (afterName := afterName.declarativeRemainder) dot.span dotParsed ?_ ?_, ?_⟩
              · simpa only [dotShape] using nameParsed
              · simpa only [frame.1, frame.2, dotShape] using argumentsRejected
              · rw [argumentsEq, nameEq, List.append_assoc]
                simp only [dotShape, State.diagnostics]

theorem dotConstructor_trace_reject_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceRejectComplete (dotConstructor nested)
      (DeclarativeGrammar.DotConstructorTraceRejects elementTrace elementRejects) := by
  intro input after diagnostic trace rejection
  cases rejection with
  | dotMissing absent reported =>
      rcases (symbol_reject_reports_iff .dot .expression).mp ⟨absent, reported⟩ with ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [dotConstructor, bind, result], rfl, reportEq, by simp⟩
  | nameRejected dotSpan dotParsed nameRejected =>
      have dotResult := symbol_eq_ok_of_exactTokenParses .dot .expression dotParsed
      rcases dotParsed with ⟨dotToken, rfl⟩
      rcases (expressionName_trace_reject_iff (input := { input with cursor := input.cursor + 1 })).mp
          nameRejected with ⟨failure, nameResult, afterEq, reportEq, events⟩
      exact ⟨failure, { input with cursor := input.cursor + 1 }, by
        simp only [dotConstructor, bind, dotResult, nameResult], afterEq.symm, reportEq,
        by simp only [events, State.diagnostics, List.append_nil]⟩
  | argumentsRejected dotSpan dotParsed nameParsed argumentsRejected =>
      rename_i afterDot afterName name nameEvents argumentEvents
      have dotResult := symbol_eq_ok_of_exactTokenParses .dot .expression dotParsed
      rcases dotParsed with ⟨dotToken, rfl⟩
      rcases expressionName_trace_success_complete (input := { input with cursor := input.cursor + 1 })
          nameParsed with ⟨next, nameResult, nextAfter, nameEq⟩
      have frame := expressionName_success_context_eq nameResult
      have argumentsAtNext : DeclarativeGrammar.OptionalDotConstructorArgumentsTraceRejects
          elementTrace elementRejects next.file.id next.window.endByte next.declarativeRemainder
          after diagnostic argumentEvents := by
        simpa only [frame.1, frame.2, nextAfter] using argumentsRejected
      rcases optionalDotConstructorArguments_trace_reject_complete successComplete rejectComplete contextFrame
          argumentsAtNext with ⟨failure, rejected, argumentsResult, afterEq, reportEq, argumentsEq⟩
      refine ⟨failure, rejected, ?_, afterEq, reportEq, ?_⟩
      · simp only [dotConstructor, bind, dotResult, nameResult, argumentsResult]
      · rw [argumentsEq, nameEq, List.append_assoc]
        rfl

theorem dotConstructor_trace_reject_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.DotConstructorTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, dotConstructor nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact dotConstructor_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases dotConstructor_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem dotConstructor_trace_reject_failure_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.DotConstructorTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, dotConstructor nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [dotConstructor_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
