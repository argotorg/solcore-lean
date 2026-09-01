import Solcore.Syntax.DeclarativeCoreExpressionLayerOutcomeGrammar

/-! Deterministic ordinary outcomes for Core conditional expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

/-- A maximal conditional tail has a unique output remainder. -/
theorem ConditionalTailParses.output_unique
    {nestedOrdinary alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : DeterministicOutcomeSpec alternativeOrdinary
      alternativeRejects)
    {input : Remainder}
    {leftCondition rightCondition leftResult rightResult : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConditionalTailParses nestedOrdinary alternativeOrdinary
      input leftCondition leftResult afterLeft)
    (rightParsed : ConditionalTailParses nestedOrdinary alternativeOrdinary
      input rightCondition rightResult afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightCondition rightResult afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => rfl
      | next rightQuestionSpan rightColonSpan rightQuestion rightThen
            rightColon rightAlternative rightTail =>
          exact False.elim (absent_conflicts_exact leftAbsent rightQuestion)
  | next leftQuestionSpan leftColonSpan leftQuestion leftThen leftColon
        leftAlternative leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftQuestion)
      | next rightQuestionSpan rightColonSpan rightQuestion rightThen
            rightColon rightAlternative rightTail =>
          have afterQuestionEq := exactToken_output_unique leftQuestion
            rightQuestion
          subst afterQuestionEq
          have afterThenEq := nestedOutcomes.successOutputUnique leftThen
            rightThen
          subst afterThenEq
          have afterColonEq := exactToken_output_unique leftColon rightColon
          subst afterColonEq
          have afterAlternativeEq := alternativeOutcomes.successOutputUnique
            leftAlternative rightAlternative
          subst afterAlternativeEq
          exact inductionHypothesis rightTail

/-- Conditional-tail rejection excludes every ordinary tail success. -/
theorem ConditionalTailRejects.disjointOrdinary
    {nestedOrdinary alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : DeterministicOutcomeSpec alternativeOrdinary
      alternativeRejects)
    {input rejected : Remainder} {condition : Syntax.Expr}
    (rejection : ConditionalTailRejects nestedOrdinary alternativeOrdinary
      nestedRejects alternativeRejects input condition rejected) :
    ¬ ∃ successfulCondition expression output,
      ConditionalTailParses nestedOrdinary alternativeOrdinary input
        successfulCondition expression output := by
  induction rejection with
  | thenRejected rejectedQuestionSpan rejectedQuestion rejectedThen =>
      rintro ⟨successfulCondition, expression, output, parsed⟩
      cases parsed with
      | done absent => exact absent_conflicts_exact absent rejectedQuestion
      | next successfulQuestionSpan successfulColonSpan successfulQuestion
            successfulThen successfulColon successfulAlternative
            successfulTail =>
          have afterQuestionEq := exactToken_output_unique rejectedQuestion
            successfulQuestion
          subst afterQuestionEq
          exact nestedOutcomes.successRejectDisjoint rejectedThen
            ⟨_, _, successfulThen⟩
  | colonMissing rejectedQuestionSpan rejectedQuestion rejectedThen
        rejectedColonAbsent =>
      rintro ⟨successfulCondition, expression, output, parsed⟩
      cases parsed with
      | done absent => exact absent_conflicts_exact absent rejectedQuestion
      | next successfulQuestionSpan successfulColonSpan successfulQuestion
            successfulThen successfulColon successfulAlternative
            successfulTail =>
          have afterQuestionEq := exactToken_output_unique rejectedQuestion
            successfulQuestion
          subst afterQuestionEq
          have afterThenEq := nestedOutcomes.successOutputUnique rejectedThen
            successfulThen
          subst afterThenEq
          exact absent_conflicts_exact rejectedColonAbsent successfulColon
  | alternativeRejected rejectedQuestionSpan rejectedColonSpan
        rejectedQuestion rejectedThen rejectedColon rejectedAlternative =>
      rintro ⟨successfulCondition, expression, output, parsed⟩
      cases parsed with
      | done absent => exact absent_conflicts_exact absent rejectedQuestion
      | next successfulQuestionSpan successfulColonSpan successfulQuestion
            successfulThen successfulColon successfulAlternative
            successfulTail =>
          have afterQuestionEq := exactToken_output_unique rejectedQuestion
            successfulQuestion
          subst afterQuestionEq
          have afterThenEq := nestedOutcomes.successOutputUnique rejectedThen
            successfulThen
          subst afterThenEq
          have afterColonEq := exactToken_output_unique rejectedColon
            successfulColon
          subst afterColonEq
          exact alternativeOutcomes.successRejectDisjoint rejectedAlternative
            ⟨_, _, successfulAlternative⟩
  | laterRejected rejectedQuestionSpan rejectedColonSpan rejectedQuestion
        rejectedThen rejectedColon rejectedAlternative rejectedTail
        inductionHypothesis =>
      rintro ⟨successfulCondition, expression, output, parsed⟩
      cases parsed with
      | done absent => exact absent_conflicts_exact absent rejectedQuestion
      | next successfulQuestionSpan successfulColonSpan successfulQuestion
            successfulThen successfulColon successfulAlternative
            successfulTail =>
          have afterQuestionEq := exactToken_output_unique rejectedQuestion
            successfulQuestion
          subst afterQuestionEq
          have afterThenEq := nestedOutcomes.successOutputUnique rejectedThen
            successfulThen
          subst afterThenEq
          have afterColonEq := exactToken_output_unique rejectedColon
            successfulColon
          subst afterColonEq
          have afterAlternativeEq := alternativeOutcomes.successOutputUnique
            rejectedAlternative successfulAlternative
          subst afterAlternativeEq
          exact inductionHypothesis ⟨_, _, _, successfulTail⟩

/-- Ordinary conditional success has a unique output remainder. -/
theorem ConditionalOrdinaryParses.output_unique
    {nestedOrdinary alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : DeterministicOutcomeSpec alternativeOrdinary
      alternativeRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConditionalOrdinaryParses nestedOrdinary alternativeOrdinary
      input left afterLeft)
    (rightParsed : ConditionalOrdinaryParses nestedOrdinary alternativeOrdinary
      input right afterRight) : afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftCondition, leftAfterCondition, leftConditionParsed, leftTail⟩
  rcases rightParsed with
    ⟨rightCondition, rightAfterCondition, rightConditionParsed, rightTail⟩
  have afterConditionEq := alternativeOutcomes.successOutputUnique
    leftConditionParsed rightConditionParsed
  subst afterConditionEq
  exact leftTail.output_unique nestedOutcomes alternativeOutcomes rightTail

/-- Complete conditional rejection excludes ordinary success. -/
theorem ConditionalRejects.disjointOrdinary
    {nestedOrdinary alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : DeterministicOutcomeSpec alternativeOrdinary
      alternativeRejects)
    {input rejected : Remainder}
    (rejection : ConditionalRejects nestedOrdinary alternativeOrdinary
      nestedRejects alternativeRejects input rejected) :
    ¬ ∃ expression output,
      ConditionalOrdinaryParses nestedOrdinary alternativeOrdinary input
        expression output := by
  rintro ⟨expression, output, condition, afterCondition, conditionParsed,
    tailParsed⟩
  cases rejection with
  | conditionRejected conditionRejected =>
      exact alternativeOutcomes.successRejectDisjoint conditionRejected
        ⟨condition, afterCondition, conditionParsed⟩
  | tailRejected rejectedCondition rejectedTail =>
      have afterConditionEq := alternativeOutcomes.successOutputUnique
        rejectedCondition conditionParsed
      subst afterConditionEq
      exact rejectedTail.disjointOrdinary nestedOutcomes alternativeOutcomes
        ⟨condition, expression, output, tailParsed⟩

/-- Construct the deterministic outcome contract for the conditional layer. -/
theorem conditionalDeterministicOutcomeSpec
    {nestedOrdinary alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects alternativeRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (alternativeOutcomes : DeterministicOutcomeSpec alternativeOrdinary
      alternativeRejects) :
    DeterministicOutcomeSpec
      (ConditionalOrdinaryParses nestedOrdinary alternativeOrdinary)
      (ConditionalRejects nestedOrdinary alternativeOrdinary nestedRejects
        alternativeRejects) where
  successOutputUnique :=
    ConditionalOrdinaryParses.output_unique nestedOutcomes alternativeOutcomes
  successRejectDisjoint :=
    ConditionalRejects.disjointOrdinary nestedOutcomes alternativeOutcomes

end Solcore.Syntax.DeclarativeGrammar
