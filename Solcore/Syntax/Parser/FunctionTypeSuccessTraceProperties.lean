import Solcore.Syntax.DeclarativeFunctionTypeTraceProperties
import Solcore.Syntax.Parser.FunctionReturnsTraceProperties

/-! Raw function success composes the actual keyword, parameters, and optional
returns. Child source/full-window preservation keeps trace coordinates aligned;
no child token-carrier or validity law is part of this exact runtime contract. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open TypeFunctionInternals

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

private theorem function_bind_ok_parts {α β : Type} {first : Parser α} {next : α → Parser β}
    {input output : State} {value : β} (result : (first >>= next) input = .ok value output) :
    ∃ item after, first input = .ok item after ∧ next item after = .ok value output := by
  cases firstResult : first input <;> simp only [bind, firstResult] at result
  case ok item after => exact ⟨item, after, rfl, result⟩
  case reject => contradiction
  case invariant => contradiction

theorem parseFunctionType_success_iff_components {input output : State} {value : TypeExpr} :
    parseFunctionType nested input = .ok value output ↔
    ∃ marker afterMarker parameters afterParameters returns,
      keyword .functionKw .typeExpr input = .ok marker afterMarker ∧
      delimited .leftParen .rightParen true nested .typeExpr .typeExpr afterMarker = .ok parameters afterParameters ∧
      parseFunctionReturns nested afterParameters = .ok returns output ∧
      value = DeclarativeGrammar.functionTypeTraceValue marker.span parameters returns := by
  constructor
  · intro result
    unfold parseFunctionType at result
    rcases function_bind_ok_parts result with ⟨marker, afterMarker, markerResult, rest⟩
    rcases function_bind_ok_parts rest with ⟨parameters, afterParameters, parametersResult, rest⟩
    rcases function_bind_ok_parts rest with ⟨returns, afterReturns, returnsResult, finished⟩
    cases finished
    exact ⟨marker, afterMarker, parameters, afterParameters, returns,
      markerResult, parametersResult, returnsResult, rfl⟩
  · rintro ⟨marker, afterMarker, parameters, afterParameters, returns,
      markerResult, parametersResult, returnsResult, rfl⟩
    simp only [parseFunctionType, bind, markerResult, parametersResult, returnsResult,
      pure, DeclarativeGrammar.functionTypeTraceValue]
    rfl

theorem parseFunctionType_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessSound (parseFunctionType nested) (DeclarativeGrammar.FunctionTypeTraceParses elementTrace) := by
  intro input output value result
  rcases parseFunctionType_success_iff_components.mp result with
    ⟨marker, afterMarker, parameters, afterParameters, returns,
      markerResult, parametersResult, returnsResult, rfl⟩
  have markerParsed := keyword_success_exactTokenParses .functionKw .typeExpr markerResult
  have markerState := (keyword_ok_tokenAt .functionKw .typeExpr markerResult).2
  subst afterMarker
  rcases delimited_trace_success_sound successSound contextFrame
      .leftParen .rightParen true .typeExpr .typeExpr parametersResult with
    ⟨parameterEvents, parametersParsed, parameterEq⟩
  have frame := delimited_success_context contextFrame
    .leftParen .rightParen true .typeExpr .typeExpr parametersResult
  rcases parseFunctionReturns_trace_success_sound successSound contextFrame returnsResult with
    ⟨returnEvents, returnsParsed, returnEq⟩
  refine ⟨parameterEvents ++ returnEvents, .parsed marker.span markerParsed parametersParsed ?_, ?_⟩
  · simpa only [frame.1, frame.2] using returnsParsed
  · rw [returnEq, parameterEq]; exact List.append_assoc _ _ _

theorem parseFunctionType_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessComplete (parseFunctionType nested) (DeclarativeGrammar.FunctionTypeTraceParses elementTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed span marker parameters returns =>
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
      rcases parseFunctionReturns_trace_success_complete successComplete contextFrame returnsAtNext with
        ⟨output, returnsResult, finalEq, returnEvents⟩
      refine ⟨output, parseFunctionType_success_iff_components.mpr
        ⟨_, _, _, _, _, markerResult, parametersResult, returnsResult, rfl⟩, finalEq, ?_⟩
      rw [returnEvents, parameterEvents]; exact List.append_assoc _ _ _

theorem parseFunctionType_success_context
    (contextFrame : ParserSuccessContext nested) : ParserSuccessContext (parseFunctionType nested) := by
  intro input output value result
  rcases parseFunctionType_success_iff_components.mp result with
    ⟨marker, afterMarker, parameters, afterParameters, returns,
      markerResult, parametersResult, returnsResult, _⟩
  have markerState := (keyword_ok_tokenAt .functionKw .typeExpr markerResult).2
  subst afterMarker
  have first := delimited_success_context contextFrame
    .leftParen .rightParen true .typeExpr .typeExpr parametersResult
  have last := parseFunctionReturns_success_context contextFrame returnsResult
  exact ⟨last.1.trans first.1, last.2.trans first.2⟩

theorem parseFunctionType_trace_success_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {value : TypeExpr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.FunctionTypeTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, parseFunctionType nested input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseFunctionType_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases parseFunctionType_trace_success_sound successSound contextFrame result with ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser
