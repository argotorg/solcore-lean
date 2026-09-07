import Solcore.Syntax.DeclarativeDotConstructorTraceProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingTraceContextProperties
import Solcore.Syntax.Parser.ExpressionDiagnosticTraceContracts
import Solcore.Syntax.Parser.Expression.Atom

/-! Exact optional-argument success. The absent branch never calls the child;
the present branch is the actual no-trailing list, with explicit child laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem optionalDotConstructorArguments_eq_none_of_absent (nested : Parser Expr)
    {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol .leftParen)) :
    optionalDotConstructorArguments nested input = .ok none input := by
  simp only [optionalDotConstructorArguments, getState, bind,
    DelimitedTraceInternals.symbol_absent .leftParen absent, Bool.false_eq_true, if_false, pure]

theorem optionalDotConstructorArguments_eq_of_present (nested : Parser Expr)
    {input : State} {span : SourceSpan}
    (opening : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .leftParen }) :
    optionalDotConstructorArguments nested input =
      match delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input with
      | .ok arguments output => .ok (some arguments) output
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  have present := DelimitedTraceInternals.symbol_present .leftParen
    (input := input) (after := { input.declarativeRemainder with cursor := input.cursor + 1 }) ⟨opening, rfl⟩
  simp only [optionalDotConstructorArguments, getState, bind, present, if_true, pure]
  cases delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input <;> rfl

theorem optionalDotConstructorArguments_trace_success_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) :
    ParserTraceSuccessSound (optionalDotConstructorArguments nested)
      (DeclarativeGrammar.OptionalDotConstructorArgumentsTraceParses elementTrace) := by
  intro input output arguments result
  by_cases present : isSymbol input .leftParen = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .expression present with ⟨token, tokenResult⟩
    rw [optionalDotConstructorArguments_eq_of_present nested
      (symbol_ok_tokenAt .leftParen .expression tokenResult).1] at result
    cases argsResult : delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input with
    | invariant error => simp [argsResult] at result
    | reject failure rejected => simp [argsResult] at result
    | ok values next =>
        simp only [argsResult] at result
        cases result
        rcases delimitedNoTrailing_success_trace_sound successSound contextFrame
          .leftParen .rightParen true .expression .expression argsResult with ⟨trace, parsed, diagnostics⟩
        exact ⟨trace, .present parsed, diagnostics⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .leftParen (Bool.eq_false_iff.mpr present)
    rw [optionalDotConstructorArguments_eq_none_of_absent nested absent] at result
    cases result
    exact ⟨[], .absent absent, by simp only [List.append_nil]⟩

theorem optionalDotConstructorArguments_trace_success_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) :
    ParserTraceSuccessComplete (optionalDotConstructorArguments nested)
      (DeclarativeGrammar.OptionalDotConstructorArgumentsTraceParses elementTrace) := by
  intro input arguments after trace parsed
  cases parsed with
  | absent absent =>
      exact ⟨input, optionalDotConstructorArguments_eq_none_of_absent nested absent, rfl,
        by simp only [List.append_nil]⟩
  | present parsed =>
      rcases (DeclarativeGrammar.OptionalDotConstructorArgumentsTraceParses.present parsed).present_token with
        ⟨span, opening⟩
      rcases delimitedNoTrailing_trace_success_complete successComplete contextFrame
          .leftParen .rightParen true .expression .expression parsed with ⟨output, result, afterEq, diagnostics⟩
      exact ⟨output, by rw [optionalDotConstructorArguments_eq_of_present nested opening, result],
        afterEq, diagnostics⟩

theorem optionalDotConstructorArguments_success_context
    (contextFrame : ExpressionSuccessContext nested) :
    ParserSuccessContext (optionalDotConstructorArguments nested) := by
  intro input output arguments result
  by_cases present : isSymbol input .leftParen = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .expression present with ⟨token, tokenResult⟩
    rw [optionalDotConstructorArguments_eq_of_present nested
      (symbol_ok_tokenAt .leftParen .expression tokenResult).1] at result
    cases argsResult : delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input with
    | invariant error => simp [argsResult] at result
    | reject failure rejected => simp [argsResult] at result
    | ok values next =>
        simp only [argsResult] at result
        cases result
        exact delimitedNoTrailing_success_context contextFrame .leftParen .rightParen true
          .expression .expression argsResult
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .leftParen (Bool.eq_false_iff.mpr present)
    rw [optionalDotConstructorArguments_eq_none_of_absent nested absent] at result
    cases result
    exact ⟨rfl, rfl⟩

theorem optionalDotConstructorArguments_trace_success_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State} {arguments : Option (DelimitedList Expr)}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalDotConstructorArgumentsTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder arguments after trace ↔
    ∃ output, optionalDotConstructorArguments nested input = .ok arguments output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact optionalDotConstructorArguments_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases optionalDotConstructorArguments_trace_success_sound successSound contextFrame result with
      ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser.ExpressionAtomInternals
