import Solcore.Syntax.DeclarativeCoreExpressionConditionalOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact right-associated conditional values with a shared initial condition. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact branch outcomes fix a conditional tail at the same initial condition. -/
theorem ConditionalTailParses.result_unique
    {nestedOrdinary alternativeOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : ExactDeterministicOutcomeSpec alternativeOrdinary alternativeRejects)
    {input : Remainder} {condition left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConditionalTailParses nestedOrdinary alternativeOrdinary
      input condition left afterLeft)
    (rightParsed : ConditionalTailParses nestedOrdinary alternativeOrdinary
      input condition right afterRight) : left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl⟩
      | next _ _ rightQuestion _ _ _ _ =>
          exact False.elim (leftAbsent ⟨_, rightQuestion.1⟩)
  | next leftQuestionSpan leftColonSpan leftQuestion leftThen leftColon
      leftAlternative leftTail ih =>
      cases rightParsed with
      | done rightAbsent => exact False.elim (rightAbsent ⟨_, leftQuestion.1⟩)
      | next rightQuestionSpan rightColonSpan rightQuestion rightThen rightColon
          rightAlternative rightTail =>
          rcases leftQuestion.result_unique rightQuestion with ⟨questionEq, questionEndEq⟩
          subst questionEq
          subst questionEndEq
          rcases nestedOutcomes.successResultUnique leftThen rightThen with ⟨thenEq, thenEndEq⟩
          subst thenEq
          subst thenEndEq
          rcases leftColon.result_unique rightColon with ⟨colonEq, colonEndEq⟩
          subst colonEq
          subst colonEndEq
          rcases alternativeOutcomes.successResultUnique leftAlternative rightAlternative with
            ⟨alternativeEq, alternativeEndEq⟩
          subst alternativeEq
          subst alternativeEndEq
          rcases ih rightTail with ⟨tailEq, finalEq⟩
          subst tailEq
          exact ⟨rfl, finalEq⟩

/-- Exact initial and nested expressions fix every conditional node and span. -/
theorem ConditionalOrdinaryParses.value_unique
    {nestedOrdinary alternativeOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : ExactDeterministicOutcomeSpec alternativeOrdinary alternativeRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConditionalOrdinaryParses nestedOrdinary alternativeOrdinary input left afterLeft)
    (rightParsed : ConditionalOrdinaryParses nestedOrdinary alternativeOrdinary input right afterRight) :
    left = right := by
  rcases leftParsed with ⟨leftCondition, leftAfter, leftConditionParsed, leftTail⟩
  rcases rightParsed with ⟨rightCondition, rightAfter, rightConditionParsed, rightTail⟩
  rcases alternativeOutcomes.successResultUnique leftConditionParsed rightConditionParsed with
    ⟨conditionEq, outputEq⟩
  subst conditionEq
  subst outputEq
  exact (leftTail.result_unique nestedOutcomes alternativeOutcomes rightTail).1

end Solcore.Syntax.DeclarativeGrammar
