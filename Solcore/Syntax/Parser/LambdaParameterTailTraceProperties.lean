import Solcore.Syntax.DeclarativeLambdaParameterTailTraceProperties
import Solcore.Syntax.Parser.ParameterSourceFrameProperties

/-! Actual ordinary/comptime lambda tails use the same typed tail and a pure
retag. Their absent-colon outcomes differ. These raw-tail laws impose no input
validity and do not cover name dispatch or public recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar FunctionParameterInternals

theorem ofFunctionParameter_eq_traceValue (parameter : FunctionParameter) :
    ofFunctionParameter parameter = lambdaParameterTraceValue parameter := rfl

theorem ordinaryLambdaParameterTail_eq_of_absent (name : Identifier) {input : State}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .colon)) :
    ordinaryLambdaParameterTail name input = .ok { span := name.span, value := .inferred name } input := by
  simp only [ordinaryLambdaParameterTail, getState, bind,
    DelimitedTraceInternals.symbol_absent .colon absent, Bool.false_eq_true, if_false, pure]

theorem ordinaryLambdaParameterTail_eq_of_present (name : Identifier) {input : State}
    (present : ∃ span, TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .colon }) :
    ordinaryLambdaParameterTail name input =
      match namedParameterTail name.span none name name.span input with
      | .ok parameter output => .ok (lambdaParameterTraceValue parameter) output
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  rcases present with ⟨span, token⟩
  have colon : ExactTokenParses (.symbol .colon) input.declarativeRemainder span
      { input.declarativeRemainder with cursor := input.cursor + 1 } := ⟨token, rfl⟩
  simp only [ordinaryLambdaParameterTail, getState, bind,
    DelimitedTraceInternals.symbol_present .colon colon, if_true, pure, ofFunctionParameter_eq_traceValue]
  cases namedParameterTail name.span none name name.span input <;> rfl

theorem ordinaryLambdaParameterTail_trace_success_sound (name : Identifier) :
    ParserTraceSuccessSound (ordinaryLambdaParameterTail name) (OrdinaryLambdaParameterTailTraceParses name) := by
  intro input output value result
  by_cases guard : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter guard with ⟨colon, colonResult⟩
    have present : ∃ span, TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .colon } :=
      ⟨colon.span, (symbol_ok_tokenAt .colon .parameter colonResult).1⟩
    rw [ordinaryLambdaParameterTail_eq_of_present name present] at result
    cases tailResult : namedParameterTail name.span none name name.span input with
    | invariant error => simp [tailResult] at result
    | reject failure rejected => simp [tailResult] at result
    | ok parameter next =>
        simp only [tailResult] at result
        cases result
        rcases namedParameterTail_trace_success_sound name.span none name name.span tailResult with ⟨trace, tail, events⟩
        exact ⟨trace, .typed present tail, events⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr guard)
    rw [ordinaryLambdaParameterTail_eq_of_absent name absent] at result
    cases result
    exact ⟨[], .inferred absent, by simp⟩

theorem ordinaryLambdaParameterTail_reject_trace_sound (name : Identifier) :
    ParserTraceRejectSound (ordinaryLambdaParameterTail name) (OrdinaryLambdaParameterTailTraceRejects name) := by
  intro input rejected failure result
  by_cases guard : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter guard with ⟨colon, colonResult⟩
    have present : ∃ span, TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .colon } :=
      ⟨colon.span, (symbol_ok_tokenAt .colon .parameter colonResult).1⟩
    rw [ordinaryLambdaParameterTail_eq_of_present name present] at result
    cases tailResult : namedParameterTail name.span none name name.span input with
    | invariant error => simp [tailResult] at result
    | ok parameter next => simp [tailResult] at result
    | reject actual next =>
        simp only [tailResult] at result
        cases result
        exact namedParameterTail_reject_trace_sound name.span none name name.span tailResult
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr guard)
    rw [ordinaryLambdaParameterTail_eq_of_absent name absent] at result
    contradiction

theorem ordinaryLambdaParameterTail_ordinary (name : Identifier) : Parser.Ordinary (ordinaryLambdaParameterTail name) := by
  intro input
  by_cases guard : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter guard with ⟨colon, colonResult⟩
    rw [ordinaryLambdaParameterTail_eq_of_present name
      ⟨colon.span, (symbol_ok_tokenAt .colon .parameter colonResult).1⟩]
    rcases namedParameterTail_ordinary name.span none name name.span input with
      ⟨parameter, output, result⟩ | ⟨failure, rejected, result⟩
    · exact .inl ⟨_, output, by rw [result]⟩
    · exact .inr ⟨failure, rejected, by rw [result]⟩
  · exact .inl ⟨_, input, ordinaryLambdaParameterTail_eq_of_absent name
      (symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr guard))⟩

theorem comptimeLambdaParameterTail_eq_of_absent (marker : Token) (name : Identifier) {input : State}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .colon)) :
    comptimeLambdaParameterTail marker name input =
      match errorParameter (SourceSpan.cover marker.span name.span) .comptimeParameterRequiresType input with
      | .ok parameter output => .ok (lambdaParameterTraceValue parameter) output
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  simp only [comptimeLambdaParameterTail, getState, bind,
    DelimitedTraceInternals.symbol_absent .colon absent, Bool.false_eq_true, if_false, pure,
    ofFunctionParameter_eq_traceValue]
  rfl

theorem comptimeLambdaParameterTail_eq_of_present (marker : Token) (name : Identifier) {input : State}
    (present : ∃ span, TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .colon }) :
    comptimeLambdaParameterTail marker name input =
      match namedParameterTail marker.span (some marker.span) name (SourceSpan.cover marker.span name.span) input with
      | .ok parameter output => .ok (lambdaParameterTraceValue parameter) output
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  rcases present with ⟨span, token⟩
  have colon : ExactTokenParses (.symbol .colon) input.declarativeRemainder span
      { input.declarativeRemainder with cursor := input.cursor + 1 } := ⟨token, rfl⟩
  simp only [comptimeLambdaParameterTail, getState, bind,
    DelimitedTraceInternals.symbol_present .colon colon, if_true, pure, ofFunctionParameter_eq_traceValue]
  cases namedParameterTail marker.span (some marker.span) name (SourceSpan.cover marker.span name.span) input <;> rfl

theorem comptimeLambdaParameterTail_trace_success_sound (marker : Token) (name : Identifier) :
    ParserTraceSuccessSound (comptimeLambdaParameterTail marker name)
      (ComptimeLambdaParameterTailTraceParses marker.span name) := by
  intro input output value result
  by_cases guard : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter guard with ⟨colon, colonResult⟩
    have present : ∃ span, TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .colon } :=
      ⟨colon.span, (symbol_ok_tokenAt .colon .parameter colonResult).1⟩
    rw [comptimeLambdaParameterTail_eq_of_present marker name present] at result
    cases tailResult : namedParameterTail marker.span (some marker.span) name (SourceSpan.cover marker.span name.span) input with
    | invariant error => simp [tailResult] at result
    | reject failure rejected => simp [tailResult] at result
    | ok parameter next =>
        simp only [tailResult] at result
        cases result
        rcases namedParameterTail_trace_success_sound marker.span (some marker.span) name
          (SourceSpan.cover marker.span name.span) tailResult with ⟨trace, tail, events⟩
        exact ⟨trace, .typed present tail, events⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr guard)
    have errorResult := errorParameter_eq_ok_of_trace (SourceSpan.cover marker.span name.span)
      .comptimeParameterRequiresType input .emitted
    simp only [comptimeLambdaParameterTail_eq_of_absent marker name absent, errorResult] at result
    cases result
    exact ⟨_, .typeMissing absent .emitted, by
      simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]⟩

theorem comptimeLambdaParameterTail_reject_trace_sound (marker : Token) (name : Identifier) :
    ParserTraceRejectSound (comptimeLambdaParameterTail marker name)
      (ComptimeLambdaParameterTailTraceRejects marker.span name) := by
  intro input rejected failure result
  by_cases guard : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter guard with ⟨colon, colonResult⟩
    have present : ∃ span, TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .colon } :=
      ⟨colon.span, (symbol_ok_tokenAt .colon .parameter colonResult).1⟩
    rw [comptimeLambdaParameterTail_eq_of_present marker name present] at result
    cases tailResult : namedParameterTail marker.span (some marker.span) name (SourceSpan.cover marker.span name.span) input with
    | invariant error => simp [tailResult] at result
    | ok parameter next => simp [tailResult] at result
    | reject actual next =>
        simp only [tailResult] at result
        cases result
        exact namedParameterTail_reject_trace_sound marker.span (some marker.span) name
          (SourceSpan.cover marker.span name.span) tailResult
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr guard)
    have errorResult := errorParameter_eq_ok_of_trace (SourceSpan.cover marker.span name.span)
      .comptimeParameterRequiresType input .emitted
    simp only [comptimeLambdaParameterTail_eq_of_absent marker name absent, errorResult] at result
    contradiction

theorem comptimeLambdaParameterTail_ordinary (marker : Token) (name : Identifier) :
    Parser.Ordinary (comptimeLambdaParameterTail marker name) := by
  intro input
  by_cases guard : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter guard with ⟨colon, colonResult⟩
    rw [comptimeLambdaParameterTail_eq_of_present marker name
      ⟨colon.span, (symbol_ok_tokenAt .colon .parameter colonResult).1⟩]
    rcases namedParameterTail_ordinary marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span) input with
      ⟨parameter, output, result⟩ | ⟨failure, rejected, result⟩
    · exact .inl ⟨_, output, by rw [result]⟩
    · exact .inr ⟨failure, rejected, by rw [result]⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr guard)
    have errorResult := errorParameter_eq_ok_of_trace (SourceSpan.cover marker.span name.span)
      .comptimeParameterRequiresType input .emitted
    exact .inl ⟨_, _, by simp only [comptimeLambdaParameterTail_eq_of_absent marker name absent, errorResult]; rfl⟩

end Solcore.Syntax.Parser.LambdaParameterInternals
