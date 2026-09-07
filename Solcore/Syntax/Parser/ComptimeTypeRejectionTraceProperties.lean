import Solcore.Syntax.DeclarativeComptimeTypeRejectionTraceGrammar
import Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.DiagnosticTraceContracts
import Solcore.Syntax.Parser.Type

/-! Raw comptime rejection reflects exactly its first failing stage, retaining
the child's events without committing its terminal report. Only closing
rejection needs a child success frame for the report's source and EOF span. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem parseComptimeType_reject_trace_sound
    {nested : Parser TypeExpr}
    {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectSound (parseComptimeType nested)
      (DeclarativeGrammar.ComptimeTypeTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  unfold parseComptimeType at result
  simp only [bind] at result
  cases markerResult : contextual .comptime .typeExpr input with
  | invariant error => simp [markerResult] at result
  | reject markerFailure markerRejected =>
      have shape := acceptToken_reject_state_shape (.contextual .comptime) .typeExpr
        (·.isContextual .comptime) markerResult
      subst markerRejected
      simp only [markerResult] at result
      cases result
      have reported := (contextual_reject_reports_iff .comptime .typeExpr).mpr ⟨failure, markerResult, rfl⟩
      exact ⟨[], .markerMissing reported.1 reported.2, by simp⟩
  | ok marker afterMarker =>
      have markerParsed := contextual_success_exactTokenParses .comptime .typeExpr markerResult
      have shape := (contextual_ok_tokenAt .comptime .typeExpr markerResult).2
      subst afterMarker
      simp only [markerResult] at result
      cases openingResult : symbol .less .typeExpr { input with cursor := input.cursor + 1 } with
      | invariant error => simp [openingResult] at result
      | reject openingFailure openingRejected =>
          have shape := symbol_reject_state_eq .less .typeExpr openingResult
          subst openingRejected
          simp only [openingResult] at result
          cases result
          have reported := (symbol_reject_reports_iff .less .typeExpr).mpr ⟨failure, openingResult, rfl⟩
          exact ⟨[], .openingMissing marker.span markerParsed reported.1 reported.2,
            by simp only [List.append_nil]; rfl⟩
      | ok opening afterOpening =>
          have openingParsed := symbol_success_exactTokenParses .less .typeExpr openingResult
          have shape := (symbol_ok_tokenAt .less .typeExpr openingResult).2
          subst afterOpening
          simp only [openingResult] at result
          cases innerResult : nested { input with cursor := input.cursor + 1 + 1 } with
          | invariant error => simp [innerResult] at result
          | reject innerFailure innerRejected =>
              simp only [innerResult] at result
              cases result
              rcases rejectSound innerResult with ⟨trace, inner, events⟩
              exact ⟨trace, .innerRejected marker.span opening.span markerParsed openingParsed inner, events⟩
          | ok inner afterInner =>
              simp only [innerResult] at result
              rcases successSound innerResult with ⟨innerEvents, innerParsed, innerEq⟩
              have innerFrame := contextFrame innerResult
              cases closingResult : symbol .greater .typeExpr afterInner with
              | invariant error => simp [closingResult] at result
              | reject closingFailure closingRejected =>
                  have shape := symbol_reject_state_eq .greater .typeExpr closingResult
                  subst closingRejected
                  simp only [closingResult] at result
                  cases result
                  have reported := (symbol_reject_reports_iff .greater .typeExpr).mpr ⟨failure, closingResult, rfl⟩
                  refine ⟨innerEvents, .closingMissing marker.span opening.span markerParsed openingParsed
                    innerParsed reported.1 ?_, innerEq⟩
                  simpa only [innerFrame.1, innerFrame.2] using reported.2
              | ok closing final => simp [closingResult, pure] at result

theorem parseComptimeType_trace_reject_complete
    {nested : Parser TypeExpr}
    {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectComplete (parseComptimeType nested)
      (DeclarativeGrammar.ComptimeTypeTraceRejects elementTrace elementRejects) := by
  intro input after report trace rejection
  cases rejection with
  | markerMissing absent reported =>
      rcases (contextual_reject_reports_iff .comptime .typeExpr).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [parseComptimeType, bind, result], rfl, reportEq, by simp⟩
  | openingMissing markerSpan marker absent reported =>
      have markerResult := contextual_eq_ok_of_exactTokenParses .comptime .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      rcases (symbol_reject_reports_iff .less .typeExpr
          (input := { input with cursor := input.cursor + 1 })).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, { input with cursor := input.cursor + 1 },
        by simp only [parseComptimeType, bind, markerResult, result], rfl, reportEq,
        by simp only [List.append_nil]; rfl⟩
  | innerRejected markerSpan openingSpan marker opening inner =>
      have markerResult := contextual_eq_ok_of_exactTokenParses .comptime .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      have openingResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr
        (input := { input with cursor := input.cursor + 1 }) opening
      rcases opening with ⟨_, rfl⟩
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 + 1 }) inner with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, by simp only [parseComptimeType, bind, markerResult, openingResult, result],
        afterEq, reportEq, events⟩
  | closingMissing markerSpan openingSpan marker opening inner absent reported =>
      have markerResult := contextual_eq_ok_of_exactTokenParses .comptime .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      have openingResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr
        (input := { input with cursor := input.cursor + 1 }) opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 + 1 }) inner with
        ⟨afterInner, innerResult, afterEq, events⟩
      have frame := contextFrame innerResult
      have absentAtInner : DeclarativeGrammar.TokenKindAbsentAt afterInner.tokens afterInner.window.endIndex
          afterInner.cursor (.symbol .greater) := by simpa only [← afterEq, State.declarativeRemainder] using absent
      have reportAtInner : DeclarativeGrammar.RejectAtReports afterInner.file.id afterInner.window.endByte
          { head := .symbol .greater, tail := [] } .typeExpr afterInner.declarativeRemainder report := by
        simpa only [frame.1, frame.2, afterEq] using reported
      rcases (symbol_reject_reports_iff .greater .typeExpr).mp ⟨absentAtInner, reportAtInner⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, afterInner,
        by simp only [parseComptimeType, bind, markerResult, openingResult, innerResult, result],
        afterEq, reportEq, events⟩

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parseComptimeType_trace_reject_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ComptimeTypeTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
    ∃ failure rejected, parseComptimeType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseComptimeType_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases parseComptimeType_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem parseComptimeType_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ComptimeTypeTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, parseComptimeType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [parseComptimeType_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩
end Solcore.Syntax.Parser
