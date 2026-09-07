import Solcore.Syntax.DeclarativeFunctionTypeRejectionTraceGrammar
import Solcore.Syntax.Parser.FunctionTypeSuccessTraceProperties
import Solcore.Syntax.Parser.FunctionReturnsRejectionTraceProperties

/-! Exact raw function failures preserve the whole returned Failure and State.
Parameters run before returns; the final pure AST construction cannot reject.
Terminal reports remain separate from ordered child diagnostic events. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open TypeFunctionInternals

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parseFunctionType_reject_iff_components {input rejected : State} {failure : Failure} :
    parseFunctionType nested input = .reject failure rejected ↔
    keyword .functionKw .typeExpr input = .reject failure rejected ∨
    (∃ marker afterMarker, keyword .functionKw .typeExpr input = .ok marker afterMarker ∧
      delimited .leftParen .rightParen true nested .typeExpr .typeExpr afterMarker = .reject failure rejected) ∨
    (∃ marker afterMarker parameters afterParameters,
      keyword .functionKw .typeExpr input = .ok marker afterMarker ∧
      delimited .leftParen .rightParen true nested .typeExpr .typeExpr afterMarker = .ok parameters afterParameters ∧
      parseFunctionReturns nested afterParameters = .reject failure rejected) := by
  constructor
  · intro result
    unfold parseFunctionType at result
    cases markerResult : keyword .functionKw .typeExpr input with
    | invariant => simp only [bind, markerResult] at result; contradiction
    | reject markerFailure markerRejected =>
        simp only [bind, markerResult] at result
        cases result
        exact .inl rfl
    | ok marker afterMarker =>
        simp only [bind, markerResult] at result
        cases parametersResult : delimited .leftParen .rightParen true nested .typeExpr .typeExpr afterMarker with
        | invariant => simp only [parametersResult] at result; contradiction
        | reject parameterFailure parameterRejected =>
            simp only [parametersResult] at result
            cases result
            exact .inr (.inl ⟨_, _, rfl, parametersResult⟩)
        | ok parameters afterParameters =>
            simp only [parametersResult] at result
            cases returnsResult : parseFunctionReturns nested afterParameters with
            | invariant => simp only [returnsResult] at result; contradiction
            | ok => simp only [returnsResult, pure] at result; contradiction
            | reject returnFailure returnRejected =>
                simp only [returnsResult] at result
                cases result
                exact .inr (.inr ⟨_, _, _, _, rfl, parametersResult, returnsResult⟩)
  · rintro (markerResult | ⟨marker, afterMarker, markerResult, parametersResult⟩ |
      ⟨marker, afterMarker, parameters, afterParameters, markerResult, parametersResult, returnsResult⟩)
    · simp only [parseFunctionType, bind, markerResult]
    · simp only [parseFunctionType, bind, markerResult, parametersResult]
    · simp only [parseFunctionType, bind, markerResult, parametersResult, returnsResult]

theorem parseFunctionType_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectSound (parseFunctionType nested)
      (DeclarativeGrammar.FunctionTypeTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  rcases parseFunctionType_reject_iff_components.mp result with markerResult |
      ⟨marker, afterMarker, markerResult, parametersResult⟩ |
      ⟨marker, afterMarker, parameters, afterParameters, markerResult, parametersResult, returnsResult⟩
  · have same := acceptToken_reject_state_shape (.keyword .functionKw) .typeExpr
      (· == .keyword .functionKw) markerResult
    subst rejected
    have reported := (keyword_reject_reports_iff .functionKw .typeExpr).mpr ⟨failure, markerResult, rfl⟩
    exact ⟨[], .markerMissing reported.1 reported.2, by simp only [List.append_nil]⟩
  · have markerParsed := keyword_success_exactTokenParses .functionKw .typeExpr markerResult
    have markerState := (keyword_ok_tokenAt .functionKw .typeExpr markerResult).2
    subst afterMarker
    rcases delimited_reject_trace_sound successSound rejectSound contextFrame
        .leftParen .rightParen true .typeExpr .typeExpr parametersResult with ⟨trace, rejected, events⟩
    exact ⟨trace, .parametersRejected marker.span markerParsed rejected, events⟩
  · have markerParsed := keyword_success_exactTokenParses .functionKw .typeExpr markerResult
    have markerState := (keyword_ok_tokenAt .functionKw .typeExpr markerResult).2
    subst afterMarker
    rcases delimited_trace_success_sound successSound contextFrame
        .leftParen .rightParen true .typeExpr .typeExpr parametersResult with
      ⟨parameterEvents, parametersParsed, parameterEq⟩
    have frame := delimited_success_context contextFrame
      .leftParen .rightParen true .typeExpr .typeExpr parametersResult
    rcases parseFunctionReturns_reject_trace_sound successSound rejectSound contextFrame returnsResult with
      ⟨returnEvents, returnsRejected, returnEq⟩
    refine ⟨parameterEvents ++ returnEvents,
      .returnsRejected marker.span markerParsed parametersParsed ?_, ?_⟩
    · simpa only [frame.1, frame.2] using returnsRejected
    · rw [returnEq, parameterEq]; exact List.append_assoc _ _ _

theorem parseFunctionType_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectComplete (parseFunctionType nested)
      (DeclarativeGrammar.FunctionTypeTraceRejects elementTrace elementRejects) := by
  intro input after report trace rejection
  cases rejection with
  | markerMissing absent reported =>
      rcases (keyword_reject_reports_iff .functionKw .typeExpr).mp ⟨absent, reported⟩ with
        ⟨failure, markerResult, reportEq⟩
      exact ⟨failure, input, parseFunctionType_reject_iff_components.mpr (.inl markerResult),
        rfl, reportEq, by simp only [List.append_nil]⟩
  | parametersRejected span marker parameters =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .functionKw .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      rcases delimited_trace_reject_complete successComplete rejectComplete contextFrame
          .leftParen .rightParen true .typeExpr .typeExpr
          (input := { input with cursor := input.cursor + 1 }) parameters with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, parseFunctionType_reject_iff_components.mpr
        (.inr (.inl ⟨_, _, markerResult, result⟩)), afterEq, reportEq, events⟩
  | returnsRejected span marker parameters returns =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .functionKw .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      rcases delimited_trace_success_complete successComplete contextFrame
          .leftParen .rightParen true .typeExpr .typeExpr
          (input := { input with cursor := input.cursor + 1 }) parameters with
        ⟨afterParameters, parametersResult, afterEq, parameterEvents⟩
      have frame := delimited_success_context contextFrame
        .leftParen .rightParen true .typeExpr .typeExpr parametersResult
      have returnsAtNext := returns
      rw [← afterEq, ← frame.1, ← frame.2] at returnsAtNext
      rcases parseFunctionReturns_trace_reject_complete successComplete rejectComplete contextFrame returnsAtNext with
        ⟨failure, rejected, returnsResult, finalEq, reportEq, returnEvents⟩
      refine ⟨failure, rejected, parseFunctionType_reject_iff_components.mpr
        (.inr (.inr ⟨_, _, _, _, markerResult, parametersResult, returnsResult⟩)), finalEq, reportEq, ?_⟩
      rw [returnEvents, parameterEvents]; exact List.append_assoc _ _ _

theorem parseFunctionType_trace_reject_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.FunctionTypeTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
    ∃ failure rejected, parseFunctionType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseFunctionType_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases parseFunctionType_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem parseFunctionType_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.FunctionTypeTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, parseFunctionType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [parseFunctionType_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
