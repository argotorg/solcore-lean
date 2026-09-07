import Solcore.Syntax.DeclarativeNamedParameterTailTraceProperties
import Solcore.Syntax.Parser.DelimitedClosingTraceProperties
import Solcore.Syntax.Parser.TypeExprTraceStateProperties
import Solcore.Syntax.Parser.TypedParameterFinishingTraceProperties

/-! Exact raw named-parameter tail execution on arbitrary states. The colon is
silent; successful type events precede finishing events. Missing colons recover
with an error parameter, whereas type rejection forwards its uncommitted report. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

variable (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
  (errorSpan : SourceSpan)

theorem namedParameterTail_eq_of_absent {input : State}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .colon)) :
    namedParameterTail start marker name errorSpan input =
      errorParameter errorSpan .namedParameterRequiresType input := by
  simp only [namedParameterTail, getState, bind,
    DelimitedTraceInternals.symbol_absent .colon absent, Bool.false_eq_true, if_false]

theorem namedParameterTail_eq_of_present {input : State} {span : SourceSpan}
    (colon : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .colon }) :
    namedParameterTail start marker name errorSpan input =
      match typeExpr { input with cursor := input.cursor + 1 } with
      | .ok type next => finishTypedParameter start marker name type next
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  have parsed : ExactTokenParses (.symbol .colon) input.declarativeRemainder span
      { input.declarativeRemainder with cursor := input.cursor + 1 } := ⟨colon, rfl⟩
  simp only [namedParameterTail, getState, bind,
    DelimitedTraceInternals.symbol_present .colon parsed, if_true,
    symbol_eq_ok_of_exactTokenParses .colon .parameter parsed]
  cases typeExpr { input with cursor := input.cursor + 1 } <;> rfl

theorem namedParameterTail_eq_ok_of_trace {input : State} {value : FunctionParameter}
    {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : NamedParameterTailTraceParses start marker name errorSpan input.file.id
      input.window.endByte input.declarativeRemainder value after trace) :
    namedParameterTail start marker name errorSpan input =
      .ok value (input.traceResult after trace) := by
  cases parsed with
  | typed colonSpan colon typeParsed finished =>
      have equation := namedParameterTail_eq_of_present start marker name errorSpan colon.1
      rcases colon with ⟨_, rfl⟩
      have typeResult := typeExpr_trace_success_state_iff.mp
        (show TypeExprTraceParses _ _
          ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder _ _ _ from typeParsed)
      simp only [equation, typeResult,
        finishTypedParameter_eq_ok_of_trace start marker name _ _ finished,
        State.traceResult, List.reverse_append, List.append_assoc]
  | typeMissing absent finished =>
      rw [namedParameterTail_eq_of_absent start marker name errorSpan absent,
        errorParameter_eq_ok_of_trace errorSpan .namedParameterRequiresType input finished]
      rfl

theorem namedParameterTail_eq_reject_of_trace {input : State} {failure : Failure}
    {after : Remainder} {trace : List ParseDiagnostic}
    (rejection : NamedParameterTailTraceRejects start marker name errorSpan input.file.id
      input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace) :
    namedParameterTail start marker name errorSpan input =
      .reject failure (input.traceResult after trace) := by
  cases rejection with
  | typeRejected colonSpan colon typeRejected =>
      have equation := namedParameterTail_eq_of_present start marker name errorSpan colon.1
      rcases colon with ⟨_, rfl⟩
      have typeResult := typeExpr_trace_reject_failure_state_iff.mp
        (show TypeExprTraceRejects _ _
          ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder _ _ _ from typeRejected)
      rw [equation, typeResult]
      rfl

theorem namedParameterTail_trace_success_sound :
    ParserTraceSuccessSound (namedParameterTail start marker name errorSpan)
      (NamedParameterTailTraceParses start marker name errorSpan) := by
  intro input output value result
  by_cases present : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter present with ⟨colon, colonResult⟩
    rw [namedParameterTail_eq_of_present start marker name errorSpan
      (symbol_ok_tokenAt .colon .parameter colonResult).1] at result
    cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typeResult] at result
    | reject failure rejected => simp [typeResult] at result
    | ok type next =>
        simp only [typeResult] at result
        rcases typeExpr_trace_success_sound typeResult with ⟨typeEvents, parsed, events⟩
        rcases finishTypedParameter_success_trace_sound start marker name type result with
          ⟨finishEvents, finished, rfl, rfl⟩
        refine ⟨typeEvents ++ finishEvents,
          .typed colon.span (symbol_success_exactTokenParses .colon .parameter colonResult)
            parsed finished, ?_⟩
        simpa only [State.diagnostics, List.reverse_append, List.reverse_reverse,
          List.append_assoc] using congrArg (· ++ finishEvents) events
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr present)
    rw [namedParameterTail_eq_of_absent start marker name errorSpan absent] at result
    rcases errorParameter_success_trace_sound errorSpan .namedParameterRequiresType result with
      ⟨trace, finished, rfl, rfl⟩
    exact ⟨trace, .typeMissing absent finished, by
      simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]⟩

theorem namedParameterTail_reject_trace_sound :
    ParserTraceRejectSound (namedParameterTail start marker name errorSpan)
      (NamedParameterTailTraceRejects start marker name errorSpan) := by
  intro input rejected failure result
  by_cases present : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter present with ⟨colon, colonResult⟩
    rw [namedParameterTail_eq_of_present start marker name errorSpan
      (symbol_ok_tokenAt .colon .parameter colonResult).1] at result
    cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typeResult] at result
    | ok type next =>
        exact False.elim (finishTypedParameter_ne_reject start marker name type next rejected failure
          (by simpa only [typeResult] using result))
    | reject actual next =>
        simp only [typeResult] at result
        cases result
        rcases typeExpr_reject_trace_sound typeResult with ⟨trace, rejection, events⟩
        exact ⟨trace, .typeRejected colon.span
          (symbol_success_exactTokenParses .colon .parameter colonResult) rejection, events⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr present)
    rw [namedParameterTail_eq_of_absent start marker name errorSpan absent] at result
    exact False.elim (errorParameter_ne_reject errorSpan .namedParameterRequiresType input rejected failure result)

theorem namedParameterTail_trace_success_complete :
    ParserTraceSuccessComplete (namedParameterTail start marker name errorSpan)
      (NamedParameterTailTraceParses start marker name errorSpan) := by
  intro input value after trace parsed
  exact ⟨_, namedParameterTail_eq_ok_of_trace start marker name errorSpan parsed,
    input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem namedParameterTail_trace_reject_complete :
    ParserTraceRejectComplete (namedParameterTail start marker name errorSpan)
      (NamedParameterTailTraceRejects start marker name errorSpan) := by
  intro input after report trace rejection
  cases rejection with
  | typeRejected colonSpan colon rejected =>
      rcases colon with ⟨token, rfl⟩
      rcases typeExpr_trace_reject_state_iff.mp
        (show TypeExprTraceRejects _ _
          ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder _ _ _ from rejected)
        with ⟨failure, result, reportEq⟩
      refine ⟨failure, input.traceResult after trace, ?_, rfl, reportEq,
        input.traceResult_diagnostics after trace⟩
      rw [namedParameterTail_eq_of_present start marker name errorSpan token, result]
      rfl

theorem namedParameterTail_ordinary : Parser.Ordinary (namedParameterTail start marker name errorSpan) := by
  intro input
  by_cases present : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter present with ⟨colon, colonResult⟩
    rw [namedParameterTail_eq_of_present start marker name errorSpan
      (symbol_ok_tokenAt .colon .parameter colonResult).1]
    rcases typeExpr_ordinary { input with cursor := input.cursor + 1 } with
      ⟨type, next, result⟩ | ⟨failure, rejected, result⟩
    · rw [result]
      rcases typedParameterFinishingTrace_exists type with ⟨trace, events⟩
      exact Or.inl ⟨_, _, finishTypedParameter_eq_ok_of_trace start marker name type next events⟩
    · exact Or.inr ⟨failure, rejected, by rw [result]⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr present)
    rw [namedParameterTail_eq_of_absent start marker name errorSpan absent]
    exact Or.inl ⟨_, _, errorParameter_eq_ok_of_trace errorSpan .namedParameterRequiresType input .emitted⟩

theorem namedParameterTail_ne_invariant (input : State) (error : ParserInvariantError) :
    namedParameterTail start marker name errorSpan input ≠ .invariant error := by
  intro failed
  rcases namedParameterTail_ordinary start marker name errorSpan input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.FunctionParameterInternals
