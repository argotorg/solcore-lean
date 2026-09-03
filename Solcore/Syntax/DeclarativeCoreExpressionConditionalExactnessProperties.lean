import Solcore.Syntax.DeclarativeCoreExpressionConditionalValueProperties

/-! Exact first-rejecting endpoints and complete conditional outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- A conditional suffix has one first-failing endpoint at each fixed condition. -/
theorem ConditionalTailRejects.output_unique
    {nestedOrdinary alternativeOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : ExactDeterministicOutcomeSpec alternativeOrdinary alternativeRejects)
    {input left right : Remainder} {condition : Syntax.Expr}
    (leftRejected : ConditionalTailRejects nestedOrdinary alternativeOrdinary
      nestedRejects alternativeRejects input condition left)
    (rightRejected : ConditionalTailRejects nestedOrdinary alternativeOrdinary
      nestedRejects alternativeRejects input condition right) : left = right := by
  induction leftRejected generalizing right with
  | thenRejected leftQuestionSpan leftQuestion leftThen =>
      cases rightRejected <;>
        grind [ExactTokenParses.result_unique,
          nestedOutcomes.rejectOutputUnique, nestedOutcomes.successRejectDisjoint]
  | colonMissing leftQuestionSpan leftQuestion leftThen leftAbsent =>
      cases rightRejected <;>
        grind [ExactTokenParses.result_unique, nestedOutcomes.successResultUnique,
          nestedOutcomes.successRejectDisjoint, absent_conflicts_exact]
  | alternativeRejected leftQuestionSpan leftColonSpan leftQuestion leftThen
      leftColon leftAlternative =>
      cases rightRejected <;>
        grind [ExactTokenParses.result_unique, nestedOutcomes.successResultUnique,
          nestedOutcomes.successRejectDisjoint, alternativeOutcomes.rejectOutputUnique,
          alternativeOutcomes.successRejectDisjoint, absent_conflicts_exact]
  | laterRejected leftQuestionSpan leftColonSpan leftQuestion leftThen leftColon
      leftAlternative leftTail ih =>
      cases rightRejected <;>
        grind [ExactTokenParses.result_unique, nestedOutcomes.successResultUnique,
          nestedOutcomes.successRejectDisjoint, alternativeOutcomes.successResultUnique,
          alternativeOutcomes.successRejectDisjoint, absent_conflicts_exact]

/-- A complete conditional has one initial-expression or suffix-rejection endpoint. -/
theorem ConditionalRejects.output_unique
    {nestedOrdinary alternativeOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : ExactDeterministicOutcomeSpec alternativeOrdinary alternativeRejects)
    {input left right : Remainder}
    (leftRejected : ConditionalRejects nestedOrdinary alternativeOrdinary
      nestedRejects alternativeRejects input left)
    (rightRejected : ConditionalRejects nestedOrdinary alternativeOrdinary
      nestedRejects alternativeRejects input right) : left = right := by
  cases leftRejected with
  | conditionRejected leftCondition =>
      cases rightRejected with
      | conditionRejected rightCondition =>
          exact alternativeOutcomes.rejectOutputUnique leftCondition rightCondition
      | tailRejected rightCondition _ =>
          exact False.elim (alternativeOutcomes.successRejectDisjoint leftCondition
            ⟨_, _, rightCondition⟩)
  | tailRejected leftCondition leftTail =>
      cases rightRejected with
      | conditionRejected rightCondition =>
          exact False.elim (alternativeOutcomes.successRejectDisjoint rightCondition
            ⟨_, _, leftCondition⟩)
      | tailRejected rightCondition rightTail =>
          rcases alternativeOutcomes.successResultUnique leftCondition rightCondition with
            ⟨conditionEq, outputEq⟩
          subst conditionEq
          subst outputEq
          exact leftTail.output_unique nestedOutcomes alternativeOutcomes rightTail

/-- Exact initial and nested operands compose into full conditional exactness. -/
theorem conditionalExactOutcomeSpec
    {nestedOrdinary alternativeOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : ExactDeterministicOutcomeSpec alternativeOrdinary alternativeRejects) :
    ExactDeterministicOutcomeSpec
      (ConditionalOrdinaryParses nestedOrdinary alternativeOrdinary)
      (ConditionalRejects nestedOrdinary alternativeOrdinary nestedRejects alternativeRejects) where
  toDeterministicOutcomeSpec := conditionalDeterministicOutcomeSpec
    nestedOutcomes.toDeterministicOutcomeSpec alternativeOutcomes.toDeterministicOutcomeSpec
  successValueUnique := ConditionalOrdinaryParses.value_unique nestedOutcomes alternativeOutcomes
  rejectOutputUnique := ConditionalRejects.output_unique nestedOutcomes alternativeOutcomes

end Solcore.Syntax.DeclarativeGrammar
