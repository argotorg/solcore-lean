import Solcore.Syntax.Parser.FunctionReturnsTracePrimitiveProperties

/-! Optional function returns compose the real trailing-enabled list contracts.
The contextual marker is silent and absence preserves the complete input state. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TypeFunctionInternals

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem parseFunctionReturns_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessSound (parseFunctionReturns nested)
      (DeclarativeGrammar.FunctionReturnsTraceParses elementTrace) := by
  intro input output values result
  by_cases present : isContextual input .returns = true
  · rcases contextual_eq_ok_of_isContextual_eq_true .returns .typeExpr present with ⟨marker, markerResult⟩
    have markerParsed := contextual_success_exactTokenParses .returns .typeExpr markerResult
    rw [parseFunctionReturns_eq_of_present nested markerParsed] at result
    cases valuesResult : delimited .leftParen .rightParen true nested .typeExpr .typeExpr
        { input with cursor := input.cursor + 1 } with
    | invariant | reject => simp [valuesResult] at result
    | ok list next =>
        simp only [valuesResult] at result
        cases result
        rcases delimited_trace_success_sound successSound contextFrame
            .leftParen .rightParen true .typeExpr .typeExpr valuesResult with ⟨trace, parsed, events⟩
        exact ⟨trace, .present marker.span markerParsed parsed, events⟩
  · have absent := contextualAbsentAt_of_isContextual_eq_false .returns (Bool.eq_false_iff.mpr present)
    rw [parseFunctionReturns_eq_none_of_absent nested absent] at result
    cases result
    exact ⟨[], .absent absent, by simp only [List.append_nil]⟩

theorem parseFunctionReturns_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessComplete (parseFunctionReturns nested)
      (DeclarativeGrammar.FunctionReturnsTraceParses elementTrace) := by
  intro input values after trace parsed
  cases parsed with
  | absent absent =>
      exact ⟨input, parseFunctionReturns_eq_none_of_absent nested absent, rfl, by simp only [List.append_nil]⟩
  | present span marker values =>
      have reduced := parseFunctionReturns_eq_of_present nested marker
      rcases marker with ⟨_, rfl⟩
      rcases delimited_trace_success_complete successComplete contextFrame
          .leftParen .rightParen true .typeExpr .typeExpr
          (input := { input with cursor := input.cursor + 1 }) values with ⟨output, result, afterEq, events⟩
      exact ⟨output, by rw [reduced, result], afterEq, events⟩

theorem parseFunctionReturns_success_context
    (contextFrame : ParserSuccessContext nested) : ParserSuccessContext (parseFunctionReturns nested) := by
  intro input output values result
  by_cases present : isContextual input .returns = true
  · rcases contextual_eq_ok_of_isContextual_eq_true .returns .typeExpr present with ⟨marker, markerResult⟩
    rw [parseFunctionReturns_eq_of_present nested
      (contextual_success_exactTokenParses .returns .typeExpr markerResult)] at result
    cases valuesResult : delimited .leftParen .rightParen true nested .typeExpr .typeExpr
        { input with cursor := input.cursor + 1 } with
    | invariant | reject => simp [valuesResult] at result
    | ok list next =>
        simp only [valuesResult] at result
        cases result
        have frame := delimited_success_context contextFrame
          .leftParen .rightParen true .typeExpr .typeExpr valuesResult
        exact frame
  · rw [parseFunctionReturns_eq_none_of_absent nested
      (contextualAbsentAt_of_isContextual_eq_false .returns (Bool.eq_false_iff.mpr present))] at result
    cases result
    exact ⟨rfl, rfl⟩

theorem parseFunctionReturns_trace_success_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {values : Option (DelimitedList TypeExpr)}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.FunctionReturnsTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder values after trace ↔
    ∃ output, parseFunctionReturns nested input = .ok values output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseFunctionReturns_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases parseFunctionReturns_trace_success_sound successSound contextFrame result with
      ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser.TypeFunctionInternals
