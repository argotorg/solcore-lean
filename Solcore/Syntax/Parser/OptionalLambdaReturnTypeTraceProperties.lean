import Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceProperties
import Solcore.Syntax.Parser.DelimitedClosingTraceProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Exact optional-return execution under explicit trace laws for the actual
type parser. The arrow is silent. Source/full-window preservation is a
separate conditional theorem and is not needed for these single-child laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {typeTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem optionalLambdaReturnType_eq_none_of_absent {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol .arrow)) :
    optionalLambdaReturnType input = .ok none input := by
  simp only [optionalLambdaReturnType, getState, bind,
    DelimitedTraceInternals.symbol_absent .arrow absent, Bool.false_eq_true, if_false, pure]

theorem optionalLambdaReturnType_eq_of_present {input : State} {span : SourceSpan}
    (arrow : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .arrow }) :
    optionalLambdaReturnType input =
      match typeExpr { input with cursor := input.cursor + 1 } with
      | .ok type output => .ok (some type) output
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  have parsed : DeclarativeGrammar.ExactTokenParses (.symbol .arrow)
      input.declarativeRemainder span
      { input.declarativeRemainder with cursor := input.cursor + 1 } := ⟨arrow, rfl⟩
  have selected := DelimitedTraceInternals.symbol_present .arrow parsed
  have arrowResult := symbol_eq_ok_of_exactTokenParses .arrow .typeExpr parsed
  simp only [optionalLambdaReturnType, getState, bind, selected, if_true, arrowResult, pure]
  cases typeExpr { input with cursor := input.cursor + 1 } <;> rfl

theorem optionalLambdaReturnType_trace_success_sound
    (successSound : ParserTraceSuccessSound typeExpr typeTrace) :
    ParserTraceSuccessSound optionalLambdaReturnType
      (DeclarativeGrammar.OptionalLambdaReturnTypeTraceParses typeTrace) := by
  intro input output value result
  by_cases present : isSymbol input .arrow = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .arrow .typeExpr present with ⟨arrow, arrowResult⟩
    rw [optionalLambdaReturnType_eq_of_present
      (symbol_ok_tokenAt .arrow .typeExpr arrowResult).1] at result
    cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typeResult] at result
    | reject failure rejected => simp [typeResult] at result
    | ok type next =>
        simp only [typeResult] at result
        cases result
        rcases successSound typeResult with ⟨trace, parsed, events⟩
        exact ⟨trace, .present arrow.span
          (symbol_success_exactTokenParses .arrow .typeExpr arrowResult) parsed, events⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .arrow (Bool.eq_false_iff.mpr present)
    rw [optionalLambdaReturnType_eq_none_of_absent absent] at result
    cases result
    exact ⟨[], .absent absent, by simp only [List.append_nil]⟩

theorem optionalLambdaReturnType_trace_success_complete
    (successComplete : ParserTraceSuccessComplete typeExpr typeTrace) :
    ParserTraceSuccessComplete optionalLambdaReturnType
      (DeclarativeGrammar.OptionalLambdaReturnTypeTraceParses typeTrace) := by
  intro input value after trace parsed
  cases parsed with
  | absent absent =>
      exact ⟨input, optionalLambdaReturnType_eq_none_of_absent absent, rfl,
        by simp only [List.append_nil]⟩
  | present span arrow type =>
      have equation := optionalLambdaReturnType_eq_of_present arrow.1
      rcases arrow with ⟨token, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) type with
        ⟨output, result, afterEq, events⟩
      exact ⟨output, by rw [equation, result], afterEq, events⟩

theorem optionalLambdaReturnType_success_context
    (contextFrame : ParserSuccessContext typeExpr) :
    ParserSuccessContext optionalLambdaReturnType := by
  intro input output value result
  by_cases present : isSymbol input .arrow = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .arrow .typeExpr present with ⟨arrow, arrowResult⟩
    rw [optionalLambdaReturnType_eq_of_present
      (symbol_ok_tokenAt .arrow .typeExpr arrowResult).1] at result
    cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typeResult] at result
    | reject failure rejected => simp [typeResult] at result
    | ok type next =>
        simp only [typeResult] at result
        cases result
        have frame := contextFrame typeResult
        exact frame
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .arrow (Bool.eq_false_iff.mpr present)
    rw [optionalLambdaReturnType_eq_none_of_absent absent] at result
    cases result
    exact ⟨rfl, rfl⟩

theorem optionalLambdaReturnType_trace_success_iff
    (successSound : ParserTraceSuccessSound typeExpr typeTrace)
    (successComplete : ParserTraceSuccessComplete typeExpr typeTrace)
    {input : State} {value : Option TypeExpr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalLambdaReturnTypeTraceParses typeTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, optionalLambdaReturnType input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact optionalLambdaReturnType_trace_success_complete successComplete
  · rintro ⟨output, result, afterEq, events⟩
    rcases optionalLambdaReturnType_trace_success_sound successSound result with
      ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

end Solcore.Syntax.Parser.ExpressionAtomInternals
