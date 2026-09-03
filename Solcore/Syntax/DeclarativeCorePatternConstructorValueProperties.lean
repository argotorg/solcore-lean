import Solcore.Syntax.DeclarativeCorePatternArgumentsExactnessProperties
import Solcore.Syntax.DeclarativeCorePatternComptimeOutcomeProperties
import Solcore.Syntax.DeclarativeCorePatternDotConstructorOutcomeProperties
import Solcore.Syntax.DeclarativeCorePatternLeafValueProperties
import Solcore.Syntax.DeclarativeCorePatternQualifiedOutcomeProperties

/-! Unique values for constructor, qualified, and compile-time patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact nested arguments fix a leading-dot constructor's complete AST. -/
theorem DotConstructorPatternOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : DotConstructorPatternOrdinaryParses nestedOrdinary nestedRejects
      input left afterLeft)
    (rightParsed : DotConstructorPatternOrdinaryParses nestedOrdinary nestedRejects
      input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftDotSpan leftDot leftName leftArguments =>
      cases rightParsed with
      | parsed rightDotSpan rightDot rightName rightArguments =>
          rcases leftDot.result_unique rightDot with ⟨dotEq, afterDotEq⟩
          subst dotEq
          subst afterDotEq
          rcases patternNameExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          have argumentsEq := leftArguments.value_unique nestedOutcomes
            rightArguments
          subst argumentsEq
          rfl

/-- Exact nested arguments and the fixed name path select one binder or
constructor value, including its source-order qualifiers. -/
theorem QualifiedPatternOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : QualifiedPatternOrdinaryParses nestedOrdinary nestedRejects
      input left afterLeft)
    (rightParsed : QualifiedPatternOrdinaryParses nestedOrdinary nestedRejects
      input right afterRight) : left = right := by
  cases leftParsed with
  | binder leftPath leftArguments leftComponents leftChoice
  | constructor leftPath leftArguments leftComponents leftChoice =>
      cases rightParsed with
      | binder rightPath rightArguments rightComponents rightChoice
      | constructor rightPath rightArguments rightComponents rightChoice =>
          rcases patternQualifiedNameExactOutcomeSpec.successResultUnique
              leftPath rightPath with ⟨pathEq, afterPathEq⟩
          subst pathEq
          subst afterPathEq
          have argumentsEq := leftArguments.value_unique nestedOutcomes
            rightArguments
          subst argumentsEq
          grind

/-- The contextual marker and exact expression value fix a comptime pattern. -/
theorem ComptimePatternOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : ComptimePatternOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ComptimePatternOrdinaryParses expressionOrdinary input right
      afterRight) : left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftExpression =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightExpression =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerEq, afterMarkerEq⟩
          subst markerEq
          subst afterMarkerEq
          have expressionEq := expressionOutcomes.successValueUnique
            leftExpression rightExpression
          subst expressionEq
          rfl

end Solcore.Syntax.DeclarativeGrammar
