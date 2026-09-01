import Solcore.Syntax.Parser.Type
import Solcore.Syntax.Parser.TypeDelimitedSoundnessProperties

/-! Success soundness for comptime, proxy, and tuple type parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {α β : Type} {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected =>
      rw [firstResult] at parsed
      contradiction
  | invariant error =>
      rw [firstResult] at parsed
      contradiction

/-- Successful comptime parsing follows the exact recursive type grammar. -/
theorem parseComptimeType_success_sound (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    {input next : State} {value : TypeExpr}
    (result : parseComptimeType nested input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold parseComptimeType at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨opening, afterOpening, openingResult, rest⟩
  rcases bind_ok_components rest with
    ⟨inner, afterInner, innerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨closing, afterClosing, closingResult, finished⟩
  cases finished
  exact .comptime marker.span opening.span closing.span
    (contextual_success_exactTokenParses .comptime .typeExpr markerResult)
    (symbol_success_exactTokenParses .less .typeExpr openingResult)
    (symbol_success_exactTokenParses .greater .typeExpr closingResult)
    rfl (nestedSound innerResult)

/-- Successful proxy parsing follows the exact recursive type grammar. -/
theorem parseProxyType_success_sound (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    {input next : State} {value : TypeExpr}
    (result : parseProxyType nested input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold parseProxyType at result
  cases markerResult : symbol .at .typeExpr input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases innerResult : nested afterMarker with
      | invariant error => simp [innerResult] at result
      | reject failure rejected => simp [innerResult] at result
      | ok inner final =>
          simp only [innerResult] at result
          cases result
          exact .proxy marker.span
            (symbol_success_exactTokenParses .at .typeExpr markerResult)
            rfl (nestedSound innerResult)

/-- Successful tuple parsing follows the exact recursive type grammar. -/
theorem parseTupleType_success_sound (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {value : TypeExpr}
    (result : parseTupleType nested input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold parseTupleType at result
  rcases bind_ok_components result with
    ⟨values, afterValues, valuesResult, finished⟩
  cases finished
  have generic := delimited_allowEmpty_trailing_success_sound
    .leftParen .rightParen nested DeclarativeGrammar.TypeExprParses
    .typeExpr .typeExpr nestedSound nestedShape valuesResult
  exact .tuple rfl
    (typeExprTrailingDelimitedListParses_of_generic generic)

end Solcore.Syntax.Parser
