import Solcore.Syntax.DeclarativeImplBodyOutcomeGrammar
import Solcore.Syntax.DeclarativeImplMethodOutcomeProperties

/-! Deterministic exact ordinary outcomes for prioritized implementation bodies. -/

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

/-- Forward ordinary implementation-method tails have one final remainder. -/
theorem ImplMethodTailOrdinaryParses.output_unique
    {input : Remainder}
    {leftMethods rightMethods : List Syntax.ImplMethod}
    {leftClosingSpan rightClosingSpan : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplMethodTailOrdinaryParses input leftMethods
      leftClosingSpan afterLeft)
    (rightParsed : ImplMethodTailOrdinaryParses input rightMethods
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
            implMethodDeterministicOutcomeSpec.successOutputUnique
              leftMethodParsed rightMethodParsed
          subst afterMethodEq
          exact inductionHypothesis rightTail

/-- Exact loop rejection excludes every ordinary implementation-method tail. -/
theorem ImplMethodTailRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ImplMethodTailRejects input rejected) :
    ¬ ∃ methods closingSpan output,
      ImplMethodTailOrdinaryParses input methods closingSpan output := by
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
          exact implMethodDeterministicOutcomeSpec.successRejectDisjoint
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
            implMethodDeterministicOutcomeSpec.successOutputUnique
              rejectedMethod successfulMethod
          subst afterMethodEq
          exact inductionHypothesis ⟨_, _, _, successfulTail⟩

/-- Prioritized implementation-method tails have deterministic and exclusive
ordinary outcomes. -/
theorem implMethodTailDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ImplMethodTailOrdinaryOutcomeParses
      ImplMethodTailRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact leftParsed.output_unique rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨tail, output, parsed⟩
    exact rejection.disjointOrdinary ⟨tail.2, tail.1, output, parsed⟩

/-- Ordinary complete implementation-body success has one final remainder. -/
theorem ImplBodyOrdinaryParses.output_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftMethods rightMethods : List Syntax.ImplMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplBodyOrdinaryParses input leftSpan leftMethods afterLeft)
    (rightParsed : ImplBodyOrdinaryParses input rightSpan rightMethods
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

/-- Exact implementation-body rejection excludes every ordinary success. -/
theorem ImplBodyRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : ImplBodyRejects input rejected) :
    ¬ ∃ bodySpan methods output,
      ImplBodyOrdinaryParses input bodySpan methods output := by
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

/-- Complete implementation bodies have deterministic and exclusive ordinary
outcomes. -/
theorem implBodyDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ImplBodyOrdinaryOutcomeParses
      ImplBodyRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact leftParsed.output_unique rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨body, output, parsed⟩
    exact rejection.disjointOrdinary ⟨body.1, body.2, output, parsed⟩

end Solcore.Syntax.DeclarativeGrammar
