import Solcore.Syntax.DeclarativeFunctionReturnsTraceProperties
import Solcore.Syntax.Parser.DelimitedTrailingTraceContextProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.Type

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
