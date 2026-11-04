import Solcore.Syntax.Internal.TypeTrace
import Solcore.Syntax.Parser.Internal.DelimitedTrace
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Parser.Internal.TypeBasics

/-!
Parser side of the traces of an optional `returns` clause: silent absence,
and exact outcomes of the trailing type list.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionReturnsTracePrimitiveProperties
/-! The optional contextual guard and marker preserve the whole state except
for the present marker's cursor step. No nested parser contract is needed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TypeFunctionInternals

theorem parseFunctionReturns_eq_none_of_absent (nested : Parser TypeExpr)
    {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
      (.identifier ContextualKeyword.returns.spelling)) :
    parseFunctionReturns nested input = .ok none input := by
  have guard : isContextual input .returns = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    rcases contextual_eq_ok_of_isContextual_eq_true .returns .typeExpr present with ⟨marker, result⟩
    exact absent ⟨marker.span, (contextual_success_exactTokenParses .returns .typeExpr result).1⟩
  simp only [parseFunctionReturns, getState, bind, guard, Bool.false_eq_true, if_false, pure]

theorem parseFunctionReturns_eq_of_present (nested : Parser TypeExpr)
    {input : State} {span : SourceSpan} {after : DeclarativeGrammar.Remainder}
    (marker : DeclarativeGrammar.ExactTokenParses (.identifier ContextualKeyword.returns.spelling)
      input.declarativeRemainder span after) :
    parseFunctionReturns nested input =
      match delimited .leftParen .rightParen true nested .typeExpr .typeExpr
          { input with cursor := input.cursor + 1 } with
      | .ok values output => .ok (some values) output
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  have present : isContextual input .returns = true := by
    have current := marker.1
    change input.cursor < input.window.endIndex ∧
      input.tokens[input.cursor]? = some { span, value := .identifier ContextualKeyword.returns.spelling } at current
    simp only [isContextual, State.peekKind?, State.peek?, current.1, if_true, current.2,
      Option.map_some, TokenKind.isContextual, beq_self_eq_true]
  have markerResult := contextual_eq_ok_of_exactTokenParses .returns .typeExpr marker
  simp only [parseFunctionReturns, getState, bind, present, if_true, markerResult, pure]
  cases delimited .leftParen .rightParen true nested .typeExpr .typeExpr
    { input with cursor := input.cursor + 1 } <;> rfl

theorem parseFunctionReturns_reject_iff_list {nested : Parser TypeExpr}
    {input rejected : State} {failure : Failure} :
    parseFunctionReturns nested input = .reject failure rejected ↔
    ∃ marker, contextual .returns .typeExpr input =
        .ok marker { input with cursor := input.cursor + 1 } ∧
      delimited .leftParen .rightParen true nested .typeExpr .typeExpr
        { input with cursor := input.cursor + 1 } = .reject failure rejected := by
  constructor
  · intro result
    by_cases present : isContextual input .returns = true
    · rcases contextual_eq_ok_of_isContextual_eq_true .returns .typeExpr present with ⟨marker, markerResult⟩
      rw [parseFunctionReturns_eq_of_present nested
        (contextual_success_exactTokenParses .returns .typeExpr markerResult)] at result
      cases valuesResult : delimited .leftParen .rightParen true nested .typeExpr .typeExpr
          { input with cursor := input.cursor + 1 } with
      | ok | invariant => simp [valuesResult] at result
      | reject valuesFailure valuesRejected =>
          simp only [valuesResult] at result
          cases result
          exact ⟨marker, markerResult, rfl⟩
    · rw [parseFunctionReturns_eq_none_of_absent nested
        (contextualAbsentAt_of_isContextual_eq_false .returns (Bool.eq_false_iff.mpr present))] at result
      contradiction
  · rintro ⟨marker, markerResult, valuesResult⟩
    rw [parseFunctionReturns_eq_of_present nested
      (contextual_success_exactTokenParses .returns .typeExpr markerResult), valuesResult]

end Solcore.Syntax.Parser.TypeFunctionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionReturnsRejectionTraceProperties
/-! A present returns marker delegates exact failure and every event to the
real trailing-enabled list. The optional guard never rejects on absence and
does not commit the terminal report or change the returned Failure. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TypeFunctionInternals

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parseFunctionReturns_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectSound (parseFunctionReturns nested)
      (DeclarativeGrammar.FunctionReturnsTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  rcases parseFunctionReturns_reject_iff_list.mp result with ⟨marker, markerResult, raw⟩
  rcases delimited_reject_trace_sound successSound rejectSound contextFrame
      .leftParen .rightParen true .typeExpr .typeExpr raw with ⟨trace, rejection, events⟩
  exact ⟨trace, .present marker.span
    (contextual_success_exactTokenParses .returns .typeExpr markerResult) rejection, events⟩

theorem parseFunctionReturns_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectComplete (parseFunctionReturns nested)
      (DeclarativeGrammar.FunctionReturnsTraceRejects elementTrace elementRejects) := by
  intro input after diagnostic trace rejection
  cases rejection with
  | present span marker values =>
      have reduced := parseFunctionReturns_eq_of_present nested marker
      rcases marker with ⟨_, rfl⟩
      rcases delimited_trace_reject_complete successComplete rejectComplete contextFrame
          .leftParen .rightParen true .typeExpr .typeExpr
          (input := { input with cursor := input.cursor + 1 }) values with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, by rw [reduced, result], afterEq, reportEq, events⟩

theorem parseFunctionReturns_trace_reject_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.FunctionReturnsTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, parseFunctionReturns nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseFunctionReturns_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases parseFunctionReturns_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem parseFunctionReturns_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.FunctionReturnsTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, parseFunctionReturns nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [parseFunctionReturns_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.TypeFunctionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionReturnsTraceProperties
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
end
