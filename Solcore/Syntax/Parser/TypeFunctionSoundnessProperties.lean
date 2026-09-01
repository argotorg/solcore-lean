import Solcore.Syntax.Parser.Type
import Solcore.Syntax.Parser.TypeDelimitedSoundnessProperties

/-! Success soundness for recursive function types and their return suffix. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem typeFunctionBind_success_components {α β : Type}
    {first : Parser α} {nextParser : α → Parser β}
    {input final : State} {value : β}
    (result : (first >>= nextParser) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        nextParser firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => nextParser firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Optional function returns retain their exact marker and recursive list. -/
theorem TypeFunctionInternals.parseFunctionReturns_success_sound
    (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {returns : Option (DelimitedList TypeExpr)}
    (result : TypeFunctionInternals.parseFunctionReturns nested input =
      .ok returns next) :
    DeclarativeGrammar.OptionalFunctionTypeReturnsParses
      input.declarativeRemainder returns next.declarativeRemainder := by
  unfold TypeFunctionInternals.parseFunctionReturns getState at result
  simp only [bind] at result
  split at result
  next hasReturns =>
    rcases typeFunctionBind_success_components result with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases typeFunctionBind_success_components rest with
      ⟨values, afterValues, valuesResult, finished⟩
    cases finished
    have markerGrammar := contextual_success_exactTokenParses
      .returns .typeExpr markerResult
    have valuesGeneric := delimited_allowEmpty_trailing_success_sound
      .leftParen .rightParen nested DeclarativeGrammar.TypeExprParses
      .typeExpr .typeExpr nestedSound nestedShape valuesResult
    exact .present marker.span markerGrammar
      (typeExprTrailingDelimitedListParses_of_generic valuesGeneric)
  next noReturns =>
    cases result
    exact .absent (by
      simpa only [State.declarativeRemainder] using
        contextualAbsentAt_of_isContextual_eq_false .returns
          (Bool.eq_false_iff.mpr noReturns))

/-- Every successful function-type parse follows the recursive type grammar. -/
theorem parseFunctionType_success_sound
    (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {value : TypeExpr}
    (result : parseFunctionType nested input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold parseFunctionType at result
  rcases typeFunctionBind_success_components result with
    ⟨keywordToken, afterKeyword, keywordResult, rest⟩
  rcases typeFunctionBind_success_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases typeFunctionBind_success_components rest with
    ⟨returns, afterReturns, returnsResult, finished⟩
  cases finished
  have keywordGrammar := keyword_success_exactTokenParses
    .functionKw .typeExpr keywordResult
  have parametersGeneric := delimited_allowEmpty_trailing_success_sound
    .leftParen .rightParen nested DeclarativeGrammar.TypeExprParses
    .typeExpr .typeExpr nestedSound nestedShape parametersResult
  have parametersGrammar :=
    typeExprTrailingDelimitedListParses_of_generic parametersGeneric
  have returnsGrammar :=
    TypeFunctionInternals.parseFunctionReturns_success_sound nested
      nestedSound nestedShape returnsResult
  exact .function keywordToken.span keywordGrammar rfl parametersGrammar
    returnsGrammar

end Solcore.Syntax.Parser
