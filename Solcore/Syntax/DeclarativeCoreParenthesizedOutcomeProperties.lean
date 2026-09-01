import Solcore.Syntax.DeclarativeCoreParenthesizedTailOutcomeProperties

/-! Deterministic ordinary outcomes for guarded Core parenthesized atoms. -/

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

/-- A parenthesized ordinary success has a unique maximal output remainder. -/
theorem ParenthesizedExpressionOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input
      left afterLeft)
    (rightParsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | empty leftOpeningSpan leftClosingSpan leftOpening leftClosing =>
      cases rightParsed with
      | empty rightOpeningSpan rightClosingSpan rightOpening rightClosing =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          exact exactToken_output_unique leftClosing rightClosing
      | group rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightElement rightProgress rightCommaAbsent
            rightClosing =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosing)
      | tuple rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightFirst rightProgress rightTail =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosing)
  | group leftOpeningSpan leftClosingSpan leftOpening leftClosingAbsent
        leftElement leftProgress leftCommaAbsent leftClosing =>
      cases rightParsed with
      | empty rightOpeningSpan rightClosingSpan rightOpening rightClosing =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosing)
      | group rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightElement rightProgress rightCommaAbsent
            rightClosing =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          have afterElementEq := nestedOutcomes.successOutputUnique leftElement
            rightElement
          subst afterElementEq
          exact exactToken_output_unique leftClosing rightClosing
      | tuple rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightFirst rightProgress rightTail =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          have afterElementEq := nestedOutcomes.successOutputUnique leftElement
            rightFirst
          subst afterElementEq
          exact False.elim
            (rightTail.comma_conflicts_absent leftCommaAbsent)
  | tuple leftOpeningSpan leftClosingSpan leftOpening leftClosingAbsent
        leftFirst leftProgress leftTail =>
      cases rightParsed with
      | empty rightOpeningSpan rightClosingSpan rightOpening rightClosing =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosing)
      | group rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightElement rightProgress rightCommaAbsent
            rightClosing =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          have afterElementEq := nestedOutcomes.successOutputUnique leftFirst
            rightElement
          subst afterElementEq
          exact False.elim
            (leftTail.comma_conflicts_absent rightCommaAbsent)
      | tuple rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightFirst rightProgress rightTail =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          have afterFirstEq := nestedOutcomes.successOutputUnique leftFirst
            rightFirst
          subst afterFirstEq
          exact ParenthesizedTupleTailParses.output_unique
            (nestedOrdinary := nestedOrdinary)
            nestedOutcomes.successOutputUnique leftTail rightTail

/-- Exact guarded parenthesized rejection excludes every ordinary success. -/
theorem ParenthesizedExpressionRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : ParenthesizedExpressionRejects nestedOrdinary nestedRejects
      input rejected) :
    ¬ ∃ expression output,
      ParenthesizedExpressionOrdinaryParses nestedOrdinary input expression
        output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | firstRejected rejectedOpeningSpan rejectedOpening rejectedClosingAbsent
        rejectedFirst =>
      cases successful with
      | empty successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosing =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | group successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact nestedOutcomes.successRejectDisjoint rejectedFirst
            ⟨_, _, successfulFirst⟩
      | tuple successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulTail =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact nestedOutcomes.successRejectDisjoint rejectedFirst
            ⟨_, _, successfulFirst⟩
  | closingMissing rejectedOpeningSpan rejectedOpening
        rejectedClosingAbsentAfterOpening rejectedFirst rejectedProgress
        rejectedCommaAbsent rejectedClosingAbsent =>
      cases successful with
      | empty successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosing =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact absent_conflicts_exact rejectedClosingAbsentAfterOpening
            successfulClosing
      | group successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterFirstEq := nestedOutcomes.successOutputUnique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | tuple successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulTail =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterFirstEq := nestedOutcomes.successOutputUnique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact successfulTail.comma_conflicts_absent rejectedCommaAbsent
  | tailRejected rejectedOpeningSpan rejectedOpening rejectedClosingAbsent
        rejectedFirst rejectedProgress rejectedTail =>
      cases successful with
      | empty successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosing =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | group successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterFirstEq := nestedOutcomes.successOutputUnique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact rejectedTail.comma_conflicts_absent successfulCommaAbsent
      | tuple successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulTail =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterFirstEq := nestedOutcomes.successOutputUnique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact rejectedTail.disjointOrdinary nestedOutcomes
            ⟨_, _, _, successfulTail⟩

/-- Lift deterministic nested expression outcomes to guarded parenthesized
atoms. -/
theorem parenthesizedExpressionDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    DeterministicOutcomeSpec
      (ParenthesizedExpressionOrdinaryParses nestedOrdinary)
      (ParenthesizedExpressionRejects nestedOrdinary nestedRejects) where
  successOutputUnique :=
    ParenthesizedExpressionOrdinaryParses.output_unique nestedOutcomes
  successRejectDisjoint :=
    ParenthesizedExpressionRejects.disjointOrdinary nestedOutcomes

end Solcore.Syntax.DeclarativeGrammar
