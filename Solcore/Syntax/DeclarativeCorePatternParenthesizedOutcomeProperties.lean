import Solcore.Syntax.DeclarativeCorePatternParenthesizedTailOutcomeProperties

/-! Deterministic ordinary outcomes for Core parenthesized patterns. -/

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

/-- A parenthesized-pattern success has a unique maximal remainder. -/
theorem ParenthesizedPatternOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : ParenthesizedPatternOrdinaryParses nestedOrdinary input left
      afterLeft)
    (rightParsed : ParenthesizedPatternOrdinaryParses nestedOrdinary input
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
          exact ParenthesizedPatternTupleTailParses.output_unique
            (nestedOrdinary := nestedOrdinary)
            nestedOutcomes.successOutputUnique leftTail rightTail

/-- Exact parenthesized-pattern rejection excludes every ordinary success. -/
theorem ParenthesizedPatternRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : ParenthesizedPatternRejects nestedOrdinary nestedRejects
      input rejected) :
    ¬ ∃ pattern output,
      ParenthesizedPatternOrdinaryParses nestedOrdinary input pattern output := by
  rintro ⟨pattern, output, successful⟩
  cases rejection with
  | openingMissing openingAbsent =>
      cases successful with
      | empty openingSpan closingSpan opening closing =>
          exact absent_conflicts_exact openingAbsent opening
      | group openingSpan closingSpan opening closingAbsent element progress
            commaAbsent closing =>
          exact absent_conflicts_exact openingAbsent opening
      | tuple openingSpan closingSpan opening closingAbsent first progress
            tail =>
          exact absent_conflicts_exact openingAbsent opening
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

/-- Lift deterministic nested pattern outcomes through parentheses. -/
theorem parenthesizedPatternDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    DeterministicOutcomeSpec
      (ParenthesizedPatternOrdinaryParses nestedOrdinary)
      (ParenthesizedPatternRejects nestedOrdinary nestedRejects) where
  successOutputUnique :=
    ParenthesizedPatternOrdinaryParses.output_unique nestedOutcomes
  successRejectDisjoint :=
    ParenthesizedPatternRejects.disjointOrdinary nestedOutcomes

end Solcore.Syntax.DeclarativeGrammar
