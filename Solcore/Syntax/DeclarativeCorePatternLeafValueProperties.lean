import Solcore.Syntax.DeclarativeCorePatternCoreOutcomeLeafProperties
import Solcore.Syntax.DeclarativeCorePatternNameOutcomeGrammar
import Solcore.Syntax.DeclarativeCorePatternQualifiedNameOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreTypeNameExactnessProperties

/-! Unique ordinary values for non-recursive Core pattern leaves and names. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem patternLiteral_value_unique {input : Remainder}
    {left right : Syntax.CoreLiteral} {afterLeft afterRight : Remainder}
    (leftParsed : CoreLiteralParses input left afterLeft)
    (rightParsed : CoreLiteralParses input right afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed <;> grind [TokenAt.token_unique]

private theorem patternBoolean_value_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : BooleanIdentifierParses input left afterLeft)
    (rightParsed : BooleanIdentifierParses input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;> grind [TokenAt.token_unique]

/-- A wildcard token fixes the complete wildcard pattern and its span. -/
theorem WildcardPatternOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : WildcardPatternOrdinaryParses input left afterLeft)
    (rightParsed : WildcardPatternOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftToken =>
      cases rightParsed with
      | parsed rightSpan rightToken =>
          have spanEq := leftToken.span_unique rightToken
          subst spanEq
          rfl

/-- A literal token fixes the literal pattern's payload and source span. -/
theorem LiteralPatternOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : LiteralPatternOrdinaryParses input left afterLeft)
    (rightParsed : LiteralPatternOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftLiteral =>
      cases rightParsed with
      | parsed rightLiteral =>
          have literalEq := patternLiteral_value_unique leftLiteral rightLiteral
          subst literalEq
          rfl

/-- A Boolean keyword fixes the binder-shaped pattern's name and span. -/
theorem BooleanBinderPatternOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : BooleanBinderPatternOrdinaryParses input left afterLeft)
    (rightParsed : BooleanBinderPatternOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftName =>
      cases rightParsed with
      | parsed rightName =>
          have nameEq := patternBoolean_value_unique leftName rightName
          subst nameEq
          rfl

/-- Boolean-first pattern names fix their exact identifier value. -/
theorem PatternNameOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternNameOrdinaryParses input left afterLeft)
    (rightParsed : PatternNameOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | boolean leftBoolean =>
      cases rightParsed with
      | boolean rightBoolean =>
          exact patternBoolean_value_unique leftBoolean rightBoolean
      | identifier trueAbsent falseAbsent rightName =>
          cases leftBoolean with
          | trueKeyword token => exact False.elim (trueAbsent ⟨_, token⟩)
          | falseKeyword token => exact False.elim (falseAbsent ⟨_, token⟩)
  | identifier trueAbsent falseAbsent leftName =>
      cases rightParsed with
      | boolean rightBoolean =>
          cases rightBoolean with
          | trueKeyword token => exact False.elim (trueAbsent ⟨_, token⟩)
          | falseKeyword token => exact False.elim (falseAbsent ⟨_, token⟩)
      | identifier rightTrueAbsent rightFalseAbsent rightName =>
          exact identifierExactOutcomeSpec.successValueUnique leftName rightName

/-- Boolean-first pattern names fix their value and final remainder. -/
theorem PatternNameOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternNameOrdinaryParses input left afterLeft)
    (rightParsed : PatternNameOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨PatternNameOrdinaryParses.value_unique leftParsed rightParsed,
    patternNameDeterministicOutcomeSpec.successOutputUnique leftParsed
      rightParsed⟩

/-- Pattern names have exact ordinary values and nonconsuming rejections. -/
theorem patternNameExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PatternNameOrdinaryParses
      PatternNameRejects where
  toDeterministicOutcomeSpec := patternNameDeterministicOutcomeSpec
  successValueUnique := PatternNameOrdinaryParses.value_unique
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    cases leftRejected
    cases rightRejected
    rfl

/-- Qualified pattern names reuse the exact maximal dotted-name contract. -/
theorem patternQualifiedNameExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PatternQualifiedNameOrdinaryParses
      PatternQualifiedNameRejects :=
  typeQualifiedNameExactOutcomeSpec

end Solcore.Syntax.DeclarativeGrammar
