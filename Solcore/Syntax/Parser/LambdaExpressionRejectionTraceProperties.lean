import Solcore.Syntax.DeclarativeLambdaExpressionTraceGrammar
import Solcore.Syntax.Parser.LambdaParametersTraceProperties
import Solcore.Syntax.Parser.OptionalLambdaReturnTypeConcreteTraceProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties

/-! Raw lambda first failures preserve parameter/return events and the exact
separate terminal report. Only the supplied block's rejection contract is
assumed; concrete parameter and type parsers need no validity premises. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {block : Parser Block}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem lambdaExpression_reject_trace_sound
    (blockSound : ParserTraceRejectSound block blockRejects) :
    ParserTraceRejectSound (lambdaExpression block) (LambdaExpressionTraceRejects blockRejects) := by
  intro input rejected failure result
  unfold lambdaExpression at result
  cases markerResult : keyword .lamKw .expression input with
  | invariant error => simp [bind, markerResult] at result
  | reject actual next =>
      simp only [bind, markerResult] at result
      cases result
      have same := acceptToken_reject_state_shape (.keyword .lamKw) .expression
        (· == .keyword .lamKw) markerResult
      subst rejected
      have reported := (keyword_reject_reports_iff .lamKw .expression).mpr ⟨failure, markerResult, rfl⟩
      exact ⟨[], .markerMissing reported.1 reported.2, by simp⟩
  | ok marker afterMarker =>
      have markerParsed := keyword_success_exactTokenParses .lamKw .expression markerResult
      have markerState := (keyword_ok_tokenAt .lamKw .expression markerResult).2
      subst afterMarker
      simp only [bind, markerResult] at result
      cases parametersResult : delimited .leftParen .rightParen true lambdaParameter .parameter .expression
          { input with cursor := input.cursor + 1 } with
      | invariant error => simp [parametersResult] at result
      | reject actual next =>
          simp only [parametersResult] at result
          cases result
          rcases lambdaParameters_reject_trace_sound parametersResult with ⟨trace, rejection, events⟩
          exact ⟨trace, .parametersRejected marker.span markerParsed rejection, events⟩
      | ok parameters afterParameters =>
          simp only [parametersResult] at result
          rcases lambdaParameters_trace_success_sound parametersResult with ⟨parameterEvents, parameterList, parameterDiag⟩
          have parameterFrame := lambdaParameters_success_context parametersResult
          cases returnResult : optionalLambdaReturnType afterParameters with
          | invariant error => simp [returnResult] at result
          | reject actual next =>
              simp only [returnResult] at result
              cases result
              rcases optionalLambdaReturnType_concrete_reject_trace_sound returnResult with ⟨returnEvents, rejection, events⟩
              refine ⟨parameterEvents ++ returnEvents, .returnTypeRejected marker.span markerParsed parameterList ?_, ?_⟩
              · simpa only [parameterFrame.1, parameterFrame.2] using rejection
              · rw [events, parameterDiag]
                exact List.append_assoc _ _ _
          | ok returnType afterReturn =>
              simp only [returnResult] at result
              rcases optionalLambdaReturnType_concrete_trace_success_sound returnResult with ⟨returnEvents, returnParsed, returnDiag⟩
              have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
              cases bodyResult : block afterReturn with
              | invariant error => simp [bodyResult] at result
              | ok body next => simp [bodyResult, pure] at result
              | reject actual next =>
                  simp only [bodyResult] at result
                  cases result
                  rcases blockSound bodyResult with ⟨bodyEvents, rejection, events⟩
                  refine ⟨(parameterEvents ++ returnEvents) ++ bodyEvents,
                    .bodyRejected (returnType := returnType) (afterReturn := afterReturn.declarativeRemainder)
                      marker.span markerParsed parameterList ?_ ?_, ?_⟩
                  · simpa only [parameterFrame.1, parameterFrame.2] using returnParsed
                  · simpa only [returnFrame.1, returnFrame.2, parameterFrame.1, parameterFrame.2] using rejection
                  · rw [events, returnDiag, parameterDiag]
                    simp only [List.append_assoc, State.diagnostics]

theorem lambdaExpression_trace_reject_complete
    (blockComplete : ParserTraceRejectComplete block blockRejects) :
    ParserTraceRejectComplete (lambdaExpression block) (LambdaExpressionTraceRejects blockRejects) := by
  intro input after report trace rejection
  cases rejection with
  | markerMissing absent reported =>
      rcases (keyword_reject_reports_iff .lamKw .expression).mp ⟨absent, reported⟩ with ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [lambdaExpression, bind, result], rfl, reportEq, by simp⟩
  | parametersRejected markerSpan marker parameters =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .lamKw .expression marker
      rcases marker with ⟨_, rfl⟩
      rcases lambdaParameters_trace_reject_complete (input := { input with cursor := input.cursor + 1 }) parameters with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, by simp only [lambdaExpression, bind, markerResult, result], afterEq, reportEq, events⟩
  | returnTypeRejected markerSpan marker parameterList returnRejected =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .lamKw .expression marker
      rcases marker with ⟨_, rfl⟩
      rcases lambdaParameters_trace_success_complete (input := { input with cursor := input.cursor + 1 }) parameterList with
        ⟨afterParameters, parametersResult, parametersEq, parameterEvents⟩
      have frame := lambdaParameters_success_context parametersResult
      have returnTrace := returnRejected
      have ownerEq : afterParameters.file.id = input.file.id := congrArg (·.id) frame.1
      have endEq : afterParameters.window.endByte = input.window.endByte := congrArg (·.endByte) frame.2
      rw [← parametersEq, ← ownerEq, ← endEq] at returnTrace
      rcases optionalLambdaReturnType_concrete_trace_reject_complete returnTrace with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      refine ⟨failure, rejected, by simp only [lambdaExpression, bind, markerResult, parametersResult, result],
        afterEq, reportEq, ?_⟩
      rw [events, parameterEvents]
      exact List.append_assoc _ _ _
  | bodyRejected markerSpan marker parameterList returnParsed bodyRejected =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .lamKw .expression marker
      rcases marker with ⟨_, rfl⟩
      rcases lambdaParameters_trace_success_complete (input := { input with cursor := input.cursor + 1 }) parameterList with
        ⟨afterParameters, parametersResult, parametersEq, parameterEvents⟩
      have parameterFrame := lambdaParameters_success_context parametersResult
      have returnTrace := returnParsed
      have ownerEq : afterParameters.file.id = input.file.id := congrArg (·.id) parameterFrame.1
      have endEq : afterParameters.window.endByte = input.window.endByte := congrArg (·.endByte) parameterFrame.2
      rw [← parametersEq, ← ownerEq, ← endEq] at returnTrace
      rcases optionalLambdaReturnType_concrete_trace_success_complete returnTrace with
        ⟨afterReturn, returnResult, returnEq, returnEvents⟩
      have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
      have bodyTrace := bodyRejected
      have bodyOwner : afterReturn.file.id = input.file.id := (congrArg (·.id) returnFrame.1).trans ownerEq
      have bodyEnd : afterReturn.window.endByte = input.window.endByte := (congrArg (·.endByte) returnFrame.2).trans endEq
      rw [← returnEq, ← bodyOwner, ← bodyEnd] at bodyTrace
      rcases blockComplete bodyTrace with ⟨failure, rejected, result, afterEq, reportEq, events⟩
      refine ⟨failure, rejected,
        by simp only [lambdaExpression, bind, markerResult, parametersResult, returnResult, result], afterEq, reportEq, ?_⟩
      rw [events, returnEvents, parameterEvents]
      simp only [List.append_assoc, State.diagnostics]

end Solcore.Syntax.Parser.ExpressionAtomInternals
