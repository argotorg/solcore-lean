import Solcore.Syntax.DeclarativeLambdaExpressionTraceGrammar
import Solcore.Syntax.Parser.LambdaParametersTraceProperties
import Solcore.Syntax.Parser.OptionalLambdaReturnTypeConcreteTraceProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveSuccessTraceProperties

/-! Raw lambda success composes the silent marker, recovering parameter list,
optional return type, and supplied block. All parameter recovery events remain
before return and body events. Only the final whole-state context law needs a
successful-block frame; trace soundness and completeness do not need one. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {block : Parser Block}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}

private theorem lambda_bind_ok_parts {α β : Type} {first : Parser α} {next : α → Parser β}
    {input output : State} {value : β} (result : (first >>= next) input = .ok value output) :
    ∃ item after, first input = .ok item after ∧ next item after = .ok value output := by
  cases firstResult : first input <;> simp only [bind, firstResult] at result
  case ok item after => exact ⟨item, after, rfl, result⟩
  case reject => contradiction
  case invariant => contradiction

theorem lambdaExpression_success_iff_components {input output : State} {value : Expr} :
    lambdaExpression block input = .ok value output ↔
    ∃ marker afterMarker parameters afterParameters returnType afterReturn body,
      keyword .lamKw .expression input = .ok marker afterMarker ∧
      (delimited .leftParen .rightParen true lambdaParameter .parameter .expression)
        afterMarker = .ok parameters afterParameters ∧
      optionalLambdaReturnType afterParameters = .ok returnType afterReturn ∧
      block afterReturn = .ok body output ∧
      value = lambdaExpressionTraceValue marker.span parameters returnType body := by
  constructor
  · intro result
    unfold lambdaExpression at result
    rcases lambda_bind_ok_parts result with ⟨marker, afterMarker, markerResult, rest⟩
    rcases lambda_bind_ok_parts rest with ⟨parameters, afterParameters, parametersResult, rest⟩
    rcases lambda_bind_ok_parts rest with ⟨returnType, afterReturn, returnResult, rest⟩
    rcases lambda_bind_ok_parts rest with ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    exact ⟨marker, afterMarker, parameters, afterParameters, returnType, afterReturn, body,
      markerResult, parametersResult, returnResult, bodyResult, rfl⟩
  · rintro ⟨marker, afterMarker, parameters, afterParameters, returnType, afterReturn, body,
      markerResult, parametersResult, returnResult, bodyResult, rfl⟩
    simp only [lambdaExpression, bind, markerResult, parametersResult, returnResult, bodyResult,
      pure, lambdaExpressionTraceValue]

theorem lambdaExpression_trace_success_sound
    (successSound : ParserTraceSuccessSound block blockTrace) :
    ParserTraceSuccessSound (lambdaExpression block) (LambdaExpressionTraceParses blockTrace) := by
  intro input output value result
  rcases lambdaExpression_success_iff_components.mp result with
    ⟨marker, afterMarker, parameters, afterParameters, returnType, afterReturn, body,
      markerResult, parametersResult, returnResult, bodyResult, rfl⟩
  have markerParsed := keyword_success_exactTokenParses .lamKw .expression markerResult
  have markerState := (keyword_ok_tokenAt .lamKw .expression markerResult).2
  subst afterMarker
  rcases lambdaParameters_trace_success_sound parametersResult with ⟨parameterEvents, parametersParsed, parameterEq⟩
  have parameterFrame := lambdaParameters_success_context parametersResult
  rcases optionalLambdaReturnType_concrete_trace_success_sound returnResult with ⟨returnEvents, returnParsed, returnEq⟩
  have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
  rcases successSound bodyResult with ⟨bodyEvents, bodyParsed, bodyEq⟩
  refine ⟨(parameterEvents ++ returnEvents) ++ bodyEvents,
    .parsed marker.span markerParsed parametersParsed
      (by simpa only [parameterFrame.1, parameterFrame.2] using returnParsed)
      (by simpa only [returnFrame.1, returnFrame.2, parameterFrame.1, parameterFrame.2] using bodyParsed), ?_⟩
  change afterParameters.diagnostics = input.diagnostics ++ parameterEvents at parameterEq
  rw [bodyEq, returnEq, parameterEq]
  simp only [List.append_assoc]

theorem lambdaExpression_trace_success_complete
    (successComplete : ParserTraceSuccessComplete block blockTrace) :
    ParserTraceSuccessComplete (lambdaExpression block) (LambdaExpressionTraceParses blockTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed markerSpan marker parametersParsed returnParsed bodyParsed =>
      rename_i afterMarker afterParameters afterReturn parameters returnType body parameterEvents returnEvents bodyEvents
      have markerResult := keyword_eq_ok_of_exactTokenParses .lamKw .expression marker
      rcases marker with ⟨_, rfl⟩
      rcases lambdaParameters_trace_success_complete
          (input := { input with cursor := input.cursor + 1 }) parametersParsed with
        ⟨afterParametersState, parametersResult, parametersAfterEq, parameterEq⟩
      have parameterFrame := lambdaParameters_success_context parametersResult
      have returnAtParameters : OptionalLambdaReturnTypeTraceParses TypeExprTraceParses
          afterParametersState.file.id afterParametersState.window.endByte
          afterParametersState.declarativeRemainder returnType afterReturn returnEvents := by
        simpa only [parameterFrame.1, parameterFrame.2, parametersAfterEq] using returnParsed
      rcases optionalLambdaReturnType_concrete_trace_success_complete returnAtParameters with
        ⟨afterReturnState, returnResult, returnAfterEq, returnEq⟩
      have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
      have bodyAtReturn : blockTrace afterReturnState.file.id afterReturnState.window.endByte
          afterReturnState.declarativeRemainder body after bodyEvents := by
        simpa only [returnFrame.1, returnFrame.2, parameterFrame.1, parameterFrame.2, returnAfterEq] using bodyParsed
      rcases successComplete bodyAtReturn with ⟨output, bodyResult, outputAfterEq, bodyEq⟩
      refine ⟨output, lambdaExpression_success_iff_components.mpr
        ⟨_, _, _, _, _, _, _, markerResult, parametersResult, returnResult, bodyResult, rfl⟩,
        outputAfterEq, ?_⟩
      change afterParametersState.diagnostics = input.diagnostics ++ parameterEvents at parameterEq
      rw [bodyEq, returnEq, parameterEq]
      simp only [List.append_assoc]

theorem lambdaExpression_success_context
    (contextFrame : ParserSuccessContext block) : ParserSuccessContext (lambdaExpression block) := by
  intro input output value result
  rcases lambdaExpression_success_iff_components.mp result with
    ⟨marker, afterMarker, parameters, afterParameters, returnType, afterReturn, body,
      markerResult, parametersResult, returnResult, bodyResult, _⟩
  have markerState := (keyword_ok_tokenAt .lamKw .expression markerResult).2
  subst afterMarker
  have parameterFrame := lambdaParameters_success_context parametersResult
  have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
  have bodyFrame := contextFrame bodyResult
  exact ⟨bodyFrame.1.trans (returnFrame.1.trans parameterFrame.1),
    bodyFrame.2.trans (returnFrame.2.trans parameterFrame.2)⟩

theorem lambdaExpression_trace_success_iff
    (successSound : ParserTraceSuccessSound block blockTrace)
    (successComplete : ParserTraceSuccessComplete block blockTrace)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaExpressionTraceParses blockTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, lambdaExpression block input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact lambdaExpression_trace_success_complete successComplete
  · rintro ⟨output, result, afterEq, events⟩
    rcases lambdaExpression_trace_success_sound successSound result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem lambdaExpression_trace_success_state_iff
    (successSound : ParserTraceSuccessSound block blockTrace)
    (successComplete : ParserTraceSuccessComplete block blockTrace)
    (contextFrame : ParserSuccessContext block)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaExpressionTraceParses blockTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      lambdaExpression block input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases lambdaExpression_trace_success_complete successComplete parsed with ⟨output, result, afterEq, events⟩
    have frame := lambdaExpression_success_context contextFrame result
    have same := State.eq_traceResult_of_fields frame.1 (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact (lambdaExpression_trace_success_iff successSound successComplete).mpr
      ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
