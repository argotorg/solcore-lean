import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties
import Solcore.Syntax.DeclarativeYulExpressionLeafExactnessProperties

/-! Exact ordinary inline-Yul expression cores, conditional on nested outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Transactional call arguments fix their complete optional list value. -/
theorem OptionalYulCallArgumentsOrdinaryParses.value_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.YulExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalYulCallArgumentsOrdinaryParses ordinaryParses
      nestedRejects input left afterLeft)
    (rightParsed : OptionalYulCallArgumentsOrdinaryParses ordinaryParses
      nestedRejects input right afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent | rewound => rfl
      | present rightPresent =>
          exact False.elim
            (leftAbsent (YulCallArgumentsParses.opening_present rightPresent))
  | rewound openingSpan openingToken leftRejected =>
      cases rightParsed with
      | absent | rewound => rfl
      | present rightPresent =>
          exact False.elim
            (leftRejected.disjointOrdinary outcomes.toDeterministicOutcomeSpec
              ⟨_, _, rightPresent⟩)
  | present leftPresent =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (rightAbsent (YulCallArgumentsParses.opening_present leftPresent))
      | rewound openingSpan openingToken rightRejected =>
          exact False.elim
            (rightRejected.disjointOrdinary outcomes.toDeterministicOutcomeSpec
              ⟨_, _, leftPresent⟩)
      | present rightPresent =>
          exact congrArg some (leftPresent.value_unique outcomes rightPresent)

/-- Transactional call arguments fix both their optional value and remainder. -/
theorem OptionalYulCallArgumentsOrdinaryParses.result_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.YulExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalYulCallArgumentsOrdinaryParses ordinaryParses
      nestedRejects input left afterLeft)
    (rightParsed : OptionalYulCallArgumentsOrdinaryParses ordinaryParses
      nestedRejects input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique outcomes rightParsed,
    leftParsed.output_unique outcomes.toDeterministicOutcomeSpec rightParsed⟩

/-- Named expressions fix the identifier/call branch and complete AST. -/
theorem YulNamedExpressionOrdinaryParses.value_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects
      input left afterLeft)
    (rightParsed : YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects
      input right afterRight) : left = right := by
  cases leftParsed with
  | identifier leftName leftArguments =>
      cases rightParsed with
      | identifier rightName rightArguments =>
          rcases leftName.result_unique rightName with ⟨nameEq, outputEq⟩
          subst nameEq
          rfl
      | call rightName rightArguments =>
          have outputEq := leftName.output_unique rightName
          subst outputEq
          have impossible := leftArguments.value_unique outcomes rightArguments
          contradiction
  | call leftName leftArguments =>
      cases rightParsed with
      | identifier rightName rightArguments =>
          have outputEq := leftName.output_unique rightName
          subst outputEq
          have impossible := leftArguments.value_unique outcomes rightArguments
          contradiction
      | call rightName rightArguments =>
          rcases leftName.result_unique rightName with ⟨nameEq, outputEq⟩
          subst nameEq
          subst outputEq
          have argumentsEq := leftArguments.value_unique outcomes rightArguments
          cases Option.some.inj argumentsEq
          rfl

/-- Named expressions fix their complete AST and final remainder. -/
theorem YulNamedExpressionOrdinaryParses.result_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects
      input left afterLeft)
    (rightParsed : YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects
      input right afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique outcomes rightParsed,
    leftParsed.output_unique outcomes.toDeterministicOutcomeSpec rightParsed⟩

/-- Literal-before-name priority fixes every ordinary Yul-expression core AST. -/
theorem YulExpressionCoreOrdinaryParses.value_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects
      input left afterLeft)
    (rightParsed : YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects
      input right afterRight) : left = right := by
  cases leftParsed with
  | literal leftLiteral =>
      cases rightParsed with
      | literal rightLiteral =>
          cases leftLiteral.value_unique rightLiteral
          rfl
      | named rightAbsent _
      | metaBacktick rightAbsent _ _
      | metaInterpolation rightAbsent _ _ =>
          exact False.elim (rightAbsent leftLiteral.startsAt)
  | named leftAbsent leftNamed =>
      cases rightParsed with
      | literal rightLiteral =>
          exact False.elim (leftAbsent rightLiteral.startsAt)
      | named _ rightNamed => exact leftNamed.value_unique outcomes rightNamed
      | metaBacktick _ rightAbsent _
      | metaInterpolation _ rightAbsent _ =>
          exact False.elim (rightAbsent leftNamed.startsAt)
  | metaBacktick leftLiteralAbsent leftNameAbsent leftToken =>
      cases rightParsed with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral.startsAt)
      | named _ rightNamed =>
          exact False.elim (leftNameAbsent rightNamed.startsAt)
      | metaBacktick _ _ rightToken
      | metaInterpolation _ _ rightToken =>
          have tokenEq := leftToken.token_unique rightToken
          grind
  | metaInterpolation leftLiteralAbsent leftNameAbsent leftToken =>
      cases rightParsed with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral.startsAt)
      | named _ rightNamed =>
          exact False.elim (leftNameAbsent rightNamed.startsAt)
      | metaBacktick _ _ rightToken
      | metaInterpolation _ _ rightToken =>
          have tokenEq := leftToken.token_unique rightToken
          grind

/-- An ordinary Yul-expression core fixes its AST and complete remainder. -/
theorem YulExpressionCoreOrdinaryParses.result_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects
      input left afterLeft)
    (rightParsed : YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects
      input right afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique outcomes rightParsed,
    leftParsed.output_unique outcomes.toDeterministicOutcomeSpec rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
