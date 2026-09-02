import Solcore.Syntax.DeclarativeContractBodyOutcomeGrammar
import Solcore.Syntax.DeclarativeContractMemberRecoveryOutcomeProperties
import Solcore.Syntax.DeclarativeContractMemberWithAttributeOutcomeProperties

/-! Deterministic exact ordinary outcomes for recovery-aware contract bodies. -/

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

/-- Preserved carrier and window evidence makes the body-loop rewind exact. -/
theorem ContractMemberRejectsWithPreservedWindow.exists_rewind_eq
    {input : Remainder}
    (rejected : ContractMemberRejectsWithPreservedWindow input) :
    ∃ failed, ContractMemberRejects input failed ∧
      { failed with cursor := input.cursor } = input := by
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  refine ⟨failed, rejection, ?_⟩
  cases input
  cases failed
  simp_all

/-- A preserved member rejection excludes every derive-aware member success. -/
theorem ContractMemberRejectsWithPreservedWindow.disjointOrdinary
    {input : Remainder}
    (rejected : ContractMemberRejectsWithPreservedWindow input) :
    ¬ ∃ member output, ContractMemberOrdinaryParses input member output := by
  rintro ⟨member, output, parsed⟩
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  exact contractMemberDeterministicOutcomeSpec.successRejectDisjoint rejection
    ⟨_, _, parsed⟩

/-- Forward recovery-aware member tails have one final remainder. -/
theorem ContractMemberTailOrdinaryParses.output_unique
    {input : Remainder}
    {leftMembers rightMembers : List Syntax.ContractMember}
    {leftClosingSpan rightClosingSpan : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberTailOrdinaryParses input leftMembers
      leftClosingSpan afterLeft)
    (rightParsed : ContractMemberTailOrdinaryParses input rightMembers
      rightClosingSpan afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightMembers rightClosingSpan afterRight with
  | close leftClosingSpan leftClosingParsed =>
      cases rightParsed with
      | close rightClosingSpan rightClosingParsed =>
          exact exactToken_output_unique leftClosingParsed rightClosingParsed
      | direct rightClosingAbsent rightInside rightMember rightProgress
            rightTail =>
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosingParsed)
      | recovered rightClosingAbsent rightInside rightMemberRejected
            rightBoundaryAbsent rightRecovery rightTail =>
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosingParsed)
  | direct leftClosingAbsent leftInside leftMember leftProgress leftTail
        inductionHypothesis =>
      cases rightParsed with
      | close rightClosingSpan rightClosingParsed =>
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosingParsed)
      | direct rightClosingAbsent rightInside rightMember rightProgress
            rightTail =>
          have afterMemberEq :=
            contractMemberDeterministicOutcomeSpec.successOutputUnique
              leftMember rightMember
          cases afterMemberEq
          exact inductionHypothesis rightTail
      | recovered rightClosingAbsent rightInside rightMemberRejected
            rightBoundaryAbsent rightRecovery rightTail =>
          exact False.elim
            (rightMemberRejected.disjointOrdinary ⟨_, _, leftMember⟩)
  | recovered leftClosingAbsent leftInside leftMemberRejected
        leftBoundaryAbsent leftRecovery leftTail inductionHypothesis =>
      cases rightParsed with
      | close rightClosingSpan rightClosingParsed =>
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosingParsed)
      | direct rightClosingAbsent rightInside rightMember rightProgress
            rightTail =>
          exact False.elim
            (leftMemberRejected.disjointOrdinary ⟨_, _, rightMember⟩)
      | recovered rightClosingAbsent rightInside rightMemberRejected
            rightBoundaryAbsent rightRecovery rightTail =>
          have afterRecoveryEq :=
            contractMemberRecoveryDeterministicOutcomeSpec.successOutputUnique
              leftRecovery rightRecovery
          cases afterRecoveryEq
          exact inductionHypothesis rightTail

/-- Exact body-loop rejection excludes every successful member tail. -/
theorem ContractMemberTailRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ContractMemberTailRejects input rejected) :
    ¬ ∃ members closingSpan output,
      ContractMemberTailOrdinaryParses input members closingSpan output := by
  induction rejection with
  | windowEnd closingAbsent atEnd =>
      rintro ⟨members, closingSpan, output, parsed⟩
      cases parsed with
      | close successfulClosingSpan successfulClosing =>
          exact absent_conflicts_exact closingAbsent successfulClosing
      | direct successfulClosingAbsent inside member progress tail =>
          exact Nat.not_lt_of_ge atEnd inside
      | recovered successfulClosingAbsent inside memberRejected boundaryAbsent
            recovery tail =>
          exact Nat.not_lt_of_ge atEnd inside
  | memberAtBoundary closingAbsent inside memberRejected boundaryPresent =>
      rintro ⟨members, closingSpan, output, parsed⟩
      cases parsed with
      | close successfulClosingSpan successfulClosing =>
          exact absent_conflicts_exact closingAbsent successfulClosing
      | direct successfulClosingAbsent successfulInside member progress tail =>
          exact memberRejected.disjointOrdinary ⟨_, _, member⟩
      | recovered successfulClosingAbsent successfulInside otherRejected
            boundaryAbsent recovery tail =>
          exact boundaryAbsent boundaryPresent
  | recoveryRejected closingAbsent inside memberRejected boundaryAbsent
        rejectedRecovery =>
      rintro ⟨members, closingSpan, output, parsed⟩
      cases parsed with
      | close successfulClosingSpan successfulClosing =>
          exact absent_conflicts_exact closingAbsent successfulClosing
      | direct successfulClosingAbsent successfulInside member progress tail =>
          exact memberRejected.disjointOrdinary ⟨_, _, member⟩
      | recovered successfulClosingAbsent successfulInside otherRejected
            successfulBoundaryAbsent recovery tail =>
          exact contractMemberRecoveryDeterministicOutcomeSpec
            |>.successRejectDisjoint rejectedRecovery ⟨_, _, recovery⟩
  | laterDirect closingAbsent inside rejectedMember rejectedProgress
        tailRejected inductionHypothesis =>
      rintro ⟨members, closingSpan, output, parsed⟩
      cases parsed with
      | close successfulClosingSpan successfulClosing =>
          exact absent_conflicts_exact closingAbsent successfulClosing
      | direct successfulClosingAbsent successfulInside successfulMember
            successfulProgress successfulTail =>
          have afterMemberEq :=
            contractMemberDeterministicOutcomeSpec.successOutputUnique
              rejectedMember successfulMember
          cases afterMemberEq
          exact inductionHypothesis ⟨_, _, _, successfulTail⟩
      | recovered successfulClosingAbsent successfulInside memberRejected
            boundaryAbsent recovery tail =>
          exact memberRejected.disjointOrdinary ⟨_, _, rejectedMember⟩
  | laterRecovered closingAbsent inside memberRejected boundaryAbsent
        rejectedRecovery tailRejected inductionHypothesis =>
      rintro ⟨members, closingSpan, output, parsed⟩
      cases parsed with
      | close successfulClosingSpan successfulClosing =>
          exact absent_conflicts_exact closingAbsent successfulClosing
      | direct successfulClosingAbsent successfulInside successfulMember
            successfulProgress successfulTail =>
          exact memberRejected.disjointOrdinary ⟨_, _, successfulMember⟩
      | recovered successfulClosingAbsent successfulInside otherRejected
            successfulBoundaryAbsent successfulRecovery successfulTail =>
          have afterRecoveryEq :=
            contractMemberRecoveryDeterministicOutcomeSpec.successOutputUnique
              rejectedRecovery successfulRecovery
          cases afterRecoveryEq
          exact inductionHypothesis ⟨_, _, _, successfulTail⟩

/-- Contract-member tails have deterministic and exclusive ordinary outcomes. -/
theorem contractMemberTailDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ContractMemberTailOrdinaryOutcomeParses
      ContractMemberTailRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact leftParsed.output_unique rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨tail, output, parsed⟩
    exact rejection.disjointOrdinary ⟨tail.2, tail.1, output, parsed⟩

/-- Complete broad contract-body success has one final remainder. -/
theorem ContractBodyOrdinaryParses.output_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftMembers rightMembers : List Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractBodyOrdinaryParses input leftSpan leftMembers afterLeft)
    (rightParsed : ContractBodyOrdinaryParses input rightSpan rightMembers
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOpeningSpan leftClosingSpan leftOpening leftMembersParsed =>
      cases rightParsed with
      | parsed rightOpeningSpan rightClosingSpan rightOpening
            rightMembersParsed =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          cases afterOpeningEq
          exact leftMembersParsed.output_unique rightMembersParsed

/-- Exact complete contract-body rejection excludes every ordinary success. -/
theorem ContractBodyRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : ContractBodyRejects input rejected) :
    ¬ ∃ bodySpan members output,
      ContractBodyOrdinaryParses input bodySpan members output := by
  rintro ⟨bodySpan, members, output, parsed⟩
  cases rejection with
  | openingMissing openingAbsent =>
      cases parsed with
      | parsed openingSpan closingSpan openingParsed membersParsed =>
          exact absent_conflicts_exact openingAbsent openingParsed
  | tailRejected rejectedOpeningSpan rejectedOpening tailRejected =>
      cases parsed with
      | parsed openingSpan closingSpan openingParsed membersParsed =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            openingParsed
          cases afterOpeningEq
          exact tailRejected.disjointOrdinary ⟨_, _, _, membersParsed⟩

/-- Complete recovery-aware contract bodies have deterministic and exclusive
ordinary outcomes. -/
theorem contractBodyDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ContractBodyOrdinaryOutcomeParses
      ContractBodyRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact leftParsed.output_unique rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨body, output, parsed⟩
    exact rejection.disjointOrdinary ⟨body.1, body.2, output, parsed⟩

end Solcore.Syntax.DeclarativeGrammar
