import Solcore.Syntax.DeclarativeTraitBodyOutcomeGrammar
import Solcore.Syntax.DeclarativeTraitMethodOutcomeProperties

/-! Deterministic exact ordinary outcomes for prioritized trait bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem absent_conflicts_present {kind : TokenKind}
    {input : Remainder}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False := by
  rcases present with ⟨span, token⟩
  exact absent ⟨span, token⟩

/-- Forward ordinary trait-method tails have one final remainder. -/
theorem TraitMethodTailOrdinaryParses.output_unique
    {input : Remainder}
    {leftMethods rightMethods : List Syntax.TraitMethod}
    {leftClosingSpan rightClosingSpan : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitMethodTailOrdinaryParses input leftMethods
      leftClosingSpan afterLeft)
    (rightParsed : TraitMethodTailOrdinaryParses input rightMethods
      rightClosingSpan afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightMethods rightClosingSpan afterRight with
  | close leftClosingSpan leftClosingParsed =>
      cases rightParsed with
      | close rightClosingSpan rightClosingParsed =>
          exact exactToken_output_unique leftClosingParsed rightClosingParsed
      | next rightClosingAbsent rightFunctionPresent rightMethodParsed
            rightProgress rightTail =>
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosingParsed)
  | next leftClosingAbsent leftFunctionPresent leftMethodParsed leftProgress
        leftTail inductionHypothesis =>
      cases rightParsed with
      | close rightClosingSpan rightClosingParsed =>
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosingParsed)
      | next rightClosingAbsent rightFunctionPresent rightMethodParsed
            rightProgress rightTail =>
          have afterMethodEq :=
            traitMethodDeterministicOutcomeSpec.successOutputUnique
              leftMethodParsed rightMethodParsed
          subst afterMethodEq
          exact inductionHypothesis rightTail

/-- Exact loop rejection excludes every ordinary trait-method tail. -/
theorem TraitMethodTailRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : TraitMethodTailRejects input rejected) :
    ¬ ∃ methods closingSpan output,
      TraitMethodTailOrdinaryParses input methods closingSpan output := by
  induction rejection with
  | unexpected closingAbsent functionAbsent =>
      rintro ⟨methods, closingSpan, output, parsed⟩
      cases parsed with
      | close successfulClosingSpan successfulClosing =>
          exact absent_conflicts_exact closingAbsent successfulClosing
      | next successfulClosingAbsent successfulFunction successfulMethod
            successfulProgress successfulTail =>
          exact absent_conflicts_present functionAbsent successfulFunction
  | methodRejected closingAbsent functionPresent methodRejected =>
      rintro ⟨methods, closingSpan, output, parsed⟩
      cases parsed with
      | close successfulClosingSpan successfulClosing =>
          exact absent_conflicts_exact closingAbsent successfulClosing
      | next successfulClosingAbsent successfulFunction successfulMethod
            successfulProgress successfulTail =>
          exact traitMethodDeterministicOutcomeSpec.successRejectDisjoint
            methodRejected ⟨_, _, successfulMethod⟩
  | laterRejected closingAbsent functionPresent rejectedMethod rejectedProgress
        tailRejected inductionHypothesis =>
      rintro ⟨methods, closingSpan, output, parsed⟩
      cases parsed with
      | close successfulClosingSpan successfulClosing =>
          exact absent_conflicts_exact closingAbsent successfulClosing
      | next successfulClosingAbsent successfulFunction successfulMethod
            successfulProgress successfulTail =>
          have afterMethodEq :=
            traitMethodDeterministicOutcomeSpec.successOutputUnique
              rejectedMethod successfulMethod
          subst afterMethodEq
          exact inductionHypothesis ⟨_, _, _, successfulTail⟩

/-- Prioritized trait-method tails have deterministic and exclusive ordinary
outcomes. -/
theorem traitMethodTailDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TraitMethodTailOrdinaryOutcomeParses
      TraitMethodTailRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact leftParsed.output_unique rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨tail, output, parsed⟩
    exact rejection.disjointOrdinary ⟨tail.2, tail.1, output, parsed⟩

/-- Ordinary complete trait-body success has one final remainder. -/
theorem TraitBodyOrdinaryParses.output_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftMethods rightMethods : List Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitBodyOrdinaryParses input leftSpan leftMethods afterLeft)
    (rightParsed : TraitBodyOrdinaryParses input rightSpan rightMethods
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOpeningSpan leftClosingSpan leftOpening leftMethodsParsed =>
      cases rightParsed with
      | parsed rightOpeningSpan rightClosingSpan rightOpening
            rightMethodsParsed =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          exact leftMethodsParsed.output_unique rightMethodsParsed

/-- Exact complete trait-body rejection excludes every ordinary success. -/
theorem TraitBodyRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : TraitBodyRejects input rejected) :
    ¬ ∃ bodySpan methods output,
      TraitBodyOrdinaryParses input bodySpan methods output := by
  rintro ⟨bodySpan, methods, output, parsed⟩
  cases rejection with
  | openingMissing openingAbsent =>
      cases parsed with
      | parsed openingSpan closingSpan openingParsed methodsParsed =>
          exact absent_conflicts_exact openingAbsent openingParsed
  | tailRejected rejectedOpeningSpan rejectedOpening tailRejected =>
      cases parsed with
      | parsed openingSpan closingSpan openingParsed methodsParsed =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            openingParsed
          subst afterOpeningEq
          exact tailRejected.disjointOrdinary ⟨_, _, _, methodsParsed⟩

/-- Complete trait bodies have deterministic and exclusive ordinary outcomes. -/
theorem traitBodyDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TraitBodyOrdinaryOutcomeParses
      TraitBodyRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact leftParsed.output_unique rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨body, output, parsed⟩
    exact rejection.disjointOrdinary ⟨body.1, body.2, output, parsed⟩

end Solcore.Syntax.DeclarativeGrammar
