import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Type

/-! Success soundness for canonical mapping type parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem mappingTypeBind_success_components {α β : Type}
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

/-- Successful mapping parsing follows its exact recursive token grammar. -/
theorem parseMappingType_success_sound
    (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    {input next : State} {resultValue : TypeExpr}
    (result : parseMappingType nested input = .ok resultValue next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder resultValue
      next.declarativeRemainder := by
  unfold parseMappingType at result
  rcases mappingTypeBind_success_components result with
    ⟨mapping, afterMapping, mappingResult, rest⟩
  rcases mappingTypeBind_success_components rest with
    ⟨opening, afterOpening, openingResult, rest⟩
  rcases mappingTypeBind_success_components rest with
    ⟨key, afterKey, keyResult, rest⟩
  rcases mappingTypeBind_success_components rest with
    ⟨arrow, afterArrow, arrowResult, rest⟩
  rcases mappingTypeBind_success_components rest with
    ⟨value, afterValue, valueResult, rest⟩
  rcases mappingTypeBind_success_components rest with
    ⟨closing, afterClosing, closingResult, finished⟩
  cases finished
  exact .mapping mapping.span opening.span arrow.span closing.span
    (contextual_success_exactTokenParses .mapping .typeExpr mappingResult)
    (symbol_success_exactTokenParses .leftParen .typeExpr openingResult)
    (symbol_success_exactTokenParses .fatArrow .typeExpr arrowResult)
    (symbol_success_exactTokenParses .rightParen .typeExpr closingResult)
    rfl (nestedSound keyResult) (nestedSound valueResult)

/-- Mapping grammar soundness composes with recursive source validity. -/
theorem parseMappingType_success_sound_and_validFor
    (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedStarts : Parser.StartsAtCurrentTokenOnSuccess nested (·.span))
    (nestedShape : Parser.PreservesTokenWindow nested)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    {input next : State} {resultValue : TypeExpr}
    (inputValid : input.ValidFor)
    (result : parseMappingType nested input = .ok resultValue next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder resultValue
        next.declarativeRemainder ∧
      TypeExpr.ValidFor input.file resultValue := by
  refine ⟨parseMappingType_success_sound nested nestedSound result, ?_⟩
  have valid := parseMappingType_validFor nested nestedValid nestedStarts
    nestedShape.preservesTokensOnSuccess nestedMonotone input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
