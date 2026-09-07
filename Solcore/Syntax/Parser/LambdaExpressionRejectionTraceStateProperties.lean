import Solcore.Syntax.Parser.LambdaExpressionRejectionTraceProperties
import Solcore.Syntax.Parser.TypeSourceFrameProperties

/-! Raw lambda rejection is exact at the suffix and complete-Failure boundary.
Whole-State reconstruction additionally states the final block's rejection
frame explicitly; it is not smuggled into the raw trace contracts. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {block : Parser Block}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem lambdaExpression_eq_reject_of_marker
    {input rejected : State} {failure : Failure}
    (markerResult : keyword .lamKw .expression input = .reject failure rejected) :
    lambdaExpression block input = .reject failure rejected := by
  simp only [lambdaExpression, bind, markerResult]

theorem lambdaExpression_eq_reject_of_parameters
    {input afterMarker rejected : State} {marker : Token} {failure : Failure}
    (markerResult : keyword .lamKw .expression input = .ok marker afterMarker)
    (parametersResult : (delimited .leftParen .rightParen true lambdaParameter .parameter .expression)
      afterMarker = .reject failure rejected) :
    lambdaExpression block input = .reject failure rejected := by
  simp only [lambdaExpression, bind, markerResult, parametersResult]

theorem lambdaExpression_eq_reject_of_return
    {input afterMarker afterParameters rejected : State} {marker : Token}
    {parameters : DelimitedList LambdaParameter} {failure : Failure}
    (markerResult : keyword .lamKw .expression input = .ok marker afterMarker)
    (parametersResult : (delimited .leftParen .rightParen true lambdaParameter .parameter .expression)
      afterMarker = .ok parameters afterParameters)
    (returnResult : optionalLambdaReturnType afterParameters = .reject failure rejected) :
    lambdaExpression block input = .reject failure rejected := by
  simp only [lambdaExpression, bind, markerResult, parametersResult, returnResult]

theorem lambdaExpression_eq_reject_of_body
    {input afterMarker afterParameters afterReturn rejected : State} {marker : Token}
    {parameters : DelimitedList LambdaParameter} {returnType : Option TypeExpr} {failure : Failure}
    (markerResult : keyword .lamKw .expression input = .ok marker afterMarker)
    (parametersResult : (delimited .leftParen .rightParen true lambdaParameter .parameter .expression)
      afterMarker = .ok parameters afterParameters)
    (returnResult : optionalLambdaReturnType afterParameters = .ok returnType afterReturn)
    (bodyResult : block afterReturn = .reject failure rejected) :
    lambdaExpression block input = .reject failure rejected := by
  simp only [lambdaExpression, bind, markerResult, parametersResult, returnResult, bodyResult]

theorem optionalLambdaReturnType_reject_context {input rejected : State} {failure : Failure}
    (result : optionalLambdaReturnType input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have typeResult := (optionalLambdaReturnType_reject_iff_type.mp result).2
  have window := typeExpr_preservesTokenWindow { input with cursor := input.cursor + 1 }
  rw [typeResult] at window
  exact ⟨typeExpr_preservesFile.file_eq_of_reject
    (input := { input with cursor := input.cursor + 1 }) typeResult, window.2⟩

theorem lambdaExpression_reject_context
    (contextFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    {input rejected : State} {failure : Failure}
    (result : lambdaExpression block input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  unfold lambdaExpression at result
  cases markerResult : keyword .lamKw .expression input with
  | invariant error => simp [bind, markerResult] at result
  | reject actual next =>
      simp only [bind, markerResult] at result
      cases result
      have same := acceptToken_reject_state_shape (.keyword .lamKw) .expression
        (· == .keyword .lamKw) markerResult
      exact ⟨congrArg State.file same, congrArg State.window same⟩
  | ok marker afterMarker =>
      have markerState := (keyword_ok_tokenAt .lamKw .expression markerResult).2
      subst afterMarker
      simp only [bind, markerResult] at result
      cases parametersResult : delimited .leftParen .rightParen true lambdaParameter .parameter .expression
          { input with cursor := input.cursor + 1 } with
      | invariant error => simp [parametersResult] at result
      | reject actual next =>
          simp only [parametersResult] at result
          cases result
          exact lambdaParameters_reject_context (input := { input with cursor := input.cursor + 1 }) parametersResult
      | ok parameters afterParameters =>
          simp only [parametersResult] at result
          have parameterFrame := lambdaParameters_success_context parametersResult
          cases returnResult : optionalLambdaReturnType afterParameters with
          | invariant error => simp [returnResult] at result
          | reject actual next =>
              simp only [returnResult] at result
              cases result
              have frame := optionalLambdaReturnType_reject_context returnResult
              exact ⟨frame.1.trans parameterFrame.1, frame.2.trans parameterFrame.2⟩
          | ok returnType afterReturn =>
              simp only [returnResult] at result
              have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
              cases bodyResult : block afterReturn with
              | invariant error => simp [bodyResult] at result
              | ok body next => simp [bodyResult, pure] at result
              | reject actual next =>
                  simp only [bodyResult] at result
                  cases result
                  have frame := contextFrame bodyResult
                  exact ⟨frame.1.trans (returnFrame.1.trans parameterFrame.1),
                    frame.2.trans (returnFrame.2.trans parameterFrame.2)⟩

theorem lambdaExpression_trace_reject_iff
    (rejectSound : ParserTraceRejectSound block blockRejects)
    (rejectComplete : ParserTraceRejectComplete block blockRejects)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    LambdaExpressionTraceRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, lambdaExpression block input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact lambdaExpression_trace_reject_complete rejectComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases lambdaExpression_reject_trace_sound rejectSound result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem lambdaExpression_trace_reject_failure_iff
    (rejectSound : ParserTraceRejectSound block blockRejects)
    (rejectComplete : ParserTraceRejectComplete block blockRejects)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    LambdaExpressionTraceRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, lambdaExpression block input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [lambdaExpression_trace_reject_iff rejectSound rejectComplete]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem lambdaExpression_trace_reject_failure_state_iff
    (rejectSound : ParserTraceRejectSound block blockRejects)
    (rejectComplete : ParserTraceRejectComplete block blockRejects)
    (contextFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    LambdaExpressionTraceRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      lambdaExpression block input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases (lambdaExpression_trace_reject_failure_iff rejectSound rejectComplete).mp rejection with
      ⟨rejected, result, afterEq, events⟩
    have frame := lambdaExpression_reject_context contextFrame result
    have same := State.eq_traceResult_of_fields frame.1 (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact (lambdaExpression_trace_reject_failure_iff rejectSound rejectComplete).mpr
      ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem lambdaExpression_trace_reject_state_iff
    (rejectSound : ParserTraceRejectSound block blockRejects)
    (rejectComplete : ParserTraceRejectComplete block blockRejects)
    (contextFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    LambdaExpressionTraceRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, lambdaExpression block input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases lambdaExpression_trace_reject_complete rejectComplete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (lambdaExpression_trace_reject_failure_state_iff rejectSound rejectComplete contextFrame).mp
      (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (lambdaExpression_trace_reject_failure_state_iff rejectSound rejectComplete contextFrame).mpr result

end Solcore.Syntax.Parser.ExpressionAtomInternals
