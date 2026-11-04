import Solcore.Syntax.Internal.ContractMemberOutcomes
import Solcore.Syntax.Internal.DeriveOutcomes
import Solcore.Syntax.Grammar.Declarations
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Internal.ParameterOutcomes
import Solcore.Syntax.Internal.SignatureOutcomes

/-!
Properties of the declarative grammar of contract bodies, contract declarations and implementations: outcomes are deterministic, and successful values and rejection points are unique. Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractMemberWithAttributeExactnessProperties
/-!
Exactness transport through public contract-member derive attachment.

The only explicit premise is exactness of the attribute-free core dispatcher.
The derive parser and pure attachment relation are already exact.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {input : Remainder}
    {kind : TokenKind}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : ContractMemberCoreTokenPresentAt input kind) : False :=
  absent present

/-- The derive-attachment layer preserves exact success values whenever its
attribute-free core has exact outcomes. -/
theorem ContractMemberOrdinaryParses.value_unique_of_core
    (coreOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberCoreOrdinaryParses ContractMemberCoreRejects)
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberOrdinaryParses input left afterLeft)
    (rightParsed : ContractMemberOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | plain leftHashAbsent leftCore =>
      cases rightParsed with
      | plain rightHashAbsent rightCore =>
          exact coreOutcomes.successValueUnique leftCore rightCore
      | derived rightHashPresent rightDerive rightCore rightAttached =>
          exact False.elim
            (absent_conflicts_token leftHashAbsent rightHashPresent)
  | derived leftHashPresent leftDerive leftCore leftAttached =>
      cases rightParsed with
      | plain rightHashAbsent rightCore =>
          exact False.elim
            (absent_conflicts_token rightHashAbsent leftHashPresent)
      | derived rightHashPresent rightDerive rightCore rightAttached =>
          rcases deriveAttributeExactOutcomeSpec.successResultUnique
              leftDerive rightDerive with
            ⟨deriveEq, afterDeriveEq⟩
          subst deriveEq
          subst afterDeriveEq
          rcases coreOutcomes.successResultUnique leftCore rightCore with
            ⟨coreEq, outputEq⟩
          subst coreEq
          exact leftAttached.output_unique rightAttached

/-- Under an exact core contract, the derive-attachment layer fixes its
contract-member AST and final remainder. -/
theorem ContractMemberOrdinaryParses.result_unique_of_core
    (coreOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberCoreOrdinaryParses ContractMemberCoreRejects)
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberOrdinaryParses input left afterLeft)
    (rightParsed : ContractMemberOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_core coreOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The derive-attachment layer preserves exact first-failure endpoints
whenever its attribute-free core has exact outcomes. -/
theorem ContractMemberRejects.output_unique_of_core
    (coreOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberCoreOrdinaryParses ContractMemberCoreRejects)
    {input left right : Remainder}
    (leftRejects : ContractMemberRejects input left)
    (rightRejects : ContractMemberRejects input right) : left = right := by
  cases leftRejects with
  | plainCoreRejected leftHashAbsent leftCoreRejects =>
      cases rightRejects with
      | plainCoreRejected rightHashAbsent rightCoreRejects =>
          exact coreOutcomes.rejectOutputUnique leftCoreRejects
            rightCoreRejects
      | deriveRejected rightHashPresent rightDeriveRejects =>
          exact False.elim
            (absent_conflicts_token leftHashAbsent rightHashPresent)
      | derivedCoreRejected rightHashPresent rightDerive rightCoreRejects =>
          exact False.elim
            (absent_conflicts_token leftHashAbsent rightHashPresent)
  | deriveRejected leftHashPresent leftDeriveRejects =>
      cases rightRejects with
      | plainCoreRejected rightHashAbsent rightCoreRejects =>
          exact False.elim
            (absent_conflicts_token rightHashAbsent leftHashPresent)
      | deriveRejected rightHashPresent rightDeriveRejects =>
          exact deriveAttributeExactOutcomeSpec.rejectOutputUnique
            leftDeriveRejects rightDeriveRejects
      | derivedCoreRejected rightHashPresent rightDerive rightCoreRejects =>
          exact False.elim
            (deriveAttributeExactOutcomeSpec.successRejectDisjoint
              leftDeriveRejects ⟨_, _, rightDerive⟩)
  | derivedCoreRejected leftHashPresent leftDerive leftCoreRejects =>
      cases rightRejects with
      | plainCoreRejected rightHashAbsent rightCoreRejects =>
          exact False.elim
            (absent_conflicts_token rightHashAbsent leftHashPresent)
      | deriveRejected rightHashPresent rightDeriveRejects =>
          exact False.elim
            (deriveAttributeExactOutcomeSpec.successRejectDisjoint
              rightDeriveRejects ⟨_, _, leftDerive⟩)
      | derivedCoreRejected rightHashPresent rightDerive
            rightCoreRejects =>
          rcases deriveAttributeExactOutcomeSpec.successResultUnique
              leftDerive rightDerive with
            ⟨deriveEq, afterDeriveEq⟩
          subst deriveEq
          subst afterDeriveEq
          exact coreOutcomes.rejectOutputUnique leftCoreRejects
            rightCoreRejects

/-- Exact contract for the complete public contract-member derive layer,
parameterized only by exactness of its attribute-free core. -/
theorem contractMemberExactOutcomeSpecOfCore
    (coreOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberCoreOrdinaryParses ContractMemberCoreRejects) :
    ExactDeterministicOutcomeSpec ContractMemberOrdinaryParses
      ContractMemberRejects where
  toDeterministicOutcomeSpec := contractMemberDeterministicOutcomeSpec
  successValueUnique :=
    ContractMemberOrdinaryParses.value_unique_of_core coreOutcomes
  rejectOutputUnique :=
    ContractMemberRejects.output_unique_of_core coreOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractBodyOutcomeProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractBodyExactnessProperties
set_option autoImplicit false
namespace Solcore.Syntax.DeclarativeGrammar
private theorem contractBody_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Exact member outcomes make a successful recovery-aware tail fix its
members, closing span, and final remainder. -/
theorem ContractMemberTailOrdinaryParses.result_unique_of_member
    (memberOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberOrdinaryParses ContractMemberRejects) :
    ∀ {input : Remainder}
      {leftMembers rightMembers : List Syntax.ContractMember}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      ContractMemberTailOrdinaryParses input leftMembers leftClosing
          afterLeft →
      ContractMemberTailOrdinaryParses input rightMembers rightClosing
          afterRight →
      leftMembers = rightMembers ∧ leftClosing = rightClosing ∧
        afterLeft = afterRight := by
  intro input leftMembers rightMembers leftClosing rightClosing afterLeft
    afterRight leftParsed
  induction leftParsed generalizing rightMembers rightClosing afterRight with
  | close leftClosing leftToken =>
      intro rightParsed
      cases rightParsed with
      | close rightClosing rightToken =>
          rcases leftToken.result_unique rightToken with
            ⟨closingEq, outputEq⟩
          exact ⟨rfl, closingEq, outputEq⟩
      | direct rightClosingAbsent rightInside rightMember rightProgress
          rightTail =>
          exact False.elim
            (contractBody_absent_conflicts_exact rightClosingAbsent leftToken)
      | recovered rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryAbsent rightRecovery rightTail =>
          exact False.elim
            (contractBody_absent_conflicts_exact rightClosingAbsent leftToken)
  | direct leftClosingAbsent leftInside leftMember leftProgress leftTail
      inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | close rightClosing rightToken =>
          exact False.elim
            (contractBody_absent_conflicts_exact leftClosingAbsent rightToken)
      | direct rightClosingAbsent rightInside rightMember rightProgress
          rightTail =>
          rcases memberOutcomes.successResultUnique leftMember rightMember with
            ⟨memberEq, afterMemberEq⟩
          subst memberEq
          subst afterMemberEq
          rcases inductionHypothesis rightTail with
            ⟨membersEq, closingEq, outputEq⟩
          subst membersEq
          exact ⟨rfl, closingEq, outputEq⟩
      | recovered rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryAbsent rightRecovery rightTail =>
          exact False.elim
            (rightMemberRejected.disjointOrdinary ⟨_, _, leftMember⟩)
  | recovered leftClosingAbsent leftInside leftMemberRejected
      leftBoundaryAbsent leftRecovery leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | close rightClosing rightToken =>
          exact False.elim
            (contractBody_absent_conflicts_exact leftClosingAbsent rightToken)
      | direct rightClosingAbsent rightInside rightMember rightProgress
          rightTail =>
          exact False.elim
            (leftMemberRejected.disjointOrdinary ⟨_, _, rightMember⟩)
      | recovered rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryAbsent rightRecovery rightTail =>
          rcases contractMemberRecoveryExactOutcomeSpec.successResultUnique
              leftRecovery rightRecovery with
            ⟨memberEq, afterRecoveryEq⟩
          subst memberEq
          subst afterRecoveryEq
          rcases inductionHypothesis rightTail with
            ⟨membersEq, closingEq, outputEq⟩
          subst membersEq
          exact ⟨rfl, closingEq, outputEq⟩

/-- Exact member outcomes fix the paired tail value. -/
theorem ContractMemberTailOrdinaryOutcomeParses.value_unique_of_member
    (memberOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberOrdinaryParses ContractMemberRejects)
    {input : Remainder}
    {left right : SourceSpan × List Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberTailOrdinaryOutcomeParses input left afterLeft)
    (rightParsed : ContractMemberTailOrdinaryOutcomeParses input right
      afterRight) : left = right := by
  rcases left with ⟨leftClosing, leftMembers⟩
  rcases right with ⟨rightClosing, rightMembers⟩
  rcases leftParsed.result_unique_of_member memberOutcomes rightParsed with
    ⟨membersEq, closingEq, outputEq⟩
  subst membersEq
  subst closingEq
  rfl

/-- Exact member outcomes fix every rejecting body-tail endpoint. -/
theorem ContractMemberTailRejects.output_unique_of_member
    (memberOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberOrdinaryParses ContractMemberRejects)
    {input left right : Remainder}
    (leftRejected : ContractMemberTailRejects input left)
    (rightRejected : ContractMemberTailRejects input right) : left = right := by
  induction leftRejected generalizing right with
  | windowEnd leftClosingAbsent leftAtEnd =>
      cases rightRejected with
      | windowEnd | memberAtBoundary => rfl
      | recoveryRejected rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryAbsent rightRecovery =>
          exact False.elim (Nat.not_lt_of_ge leftAtEnd rightInside)
      | laterDirect rightClosingAbsent rightInside rightMember rightProgress
          rightTail =>
          exact False.elim (Nat.not_lt_of_ge leftAtEnd rightInside)
      | laterRecovered rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryAbsent rightRecovery rightTail =>
          exact False.elim (Nat.not_lt_of_ge leftAtEnd rightInside)
  | memberAtBoundary leftClosingAbsent leftInside leftMemberRejected
      leftBoundaryPresent =>
      cases rightRejected with
      | windowEnd | memberAtBoundary => rfl
      | recoveryRejected rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryAbsent rightRecovery =>
          exact False.elim (rightBoundaryAbsent leftBoundaryPresent)
      | laterDirect rightClosingAbsent rightInside rightMember rightProgress
          rightTail =>
          exact False.elim
            (leftMemberRejected.disjointOrdinary ⟨_, _, rightMember⟩)
      | laterRecovered rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryAbsent rightRecovery rightTail =>
          exact False.elim (rightBoundaryAbsent leftBoundaryPresent)
  | recoveryRejected leftClosingAbsent leftInside leftMemberRejected
      leftBoundaryAbsent leftRecovery =>
      cases rightRejected with
      | windowEnd rightClosingAbsent rightAtEnd =>
          exact False.elim (Nat.not_lt_of_ge rightAtEnd leftInside)
      | memberAtBoundary rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryPresent =>
          exact False.elim (leftBoundaryAbsent rightBoundaryPresent)
      | recoveryRejected rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryAbsent rightRecovery =>
          exact contractMemberRecoveryExactOutcomeSpec.rejectOutputUnique
            leftRecovery rightRecovery
      | laterDirect rightClosingAbsent rightInside rightMember rightProgress
          rightTail =>
          exact False.elim
            (leftMemberRejected.disjointOrdinary ⟨_, _, rightMember⟩)
      | laterRecovered rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryAbsent rightRecovery rightTail =>
          exact False.elim
            (contractMemberRecoveryExactOutcomeSpec.successRejectDisjoint
              leftRecovery ⟨_, _, rightRecovery⟩)
  | laterDirect leftClosingAbsent leftInside leftMember leftProgress leftTail
      inductionHypothesis =>
      cases rightRejected with
      | windowEnd rightClosingAbsent rightAtEnd =>
          exact False.elim (Nat.not_lt_of_ge rightAtEnd leftInside)
      | memberAtBoundary rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryPresent =>
          exact False.elim
            (rightMemberRejected.disjointOrdinary ⟨_, _, leftMember⟩)
      | recoveryRejected rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryAbsent rightRecovery =>
          exact False.elim
            (rightMemberRejected.disjointOrdinary ⟨_, _, leftMember⟩)
      | laterDirect rightClosingAbsent rightInside rightMember rightProgress
          rightTail =>
          have afterMemberEq := memberOutcomes.successOutputUnique leftMember
            rightMember
          subst afterMemberEq
          exact inductionHypothesis rightTail
      | laterRecovered rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryAbsent rightRecovery rightTail =>
          exact False.elim
            (rightMemberRejected.disjointOrdinary ⟨_, _, leftMember⟩)
  | laterRecovered leftClosingAbsent leftInside leftMemberRejected
      leftBoundaryAbsent leftRecovery leftTail inductionHypothesis =>
      cases rightRejected with
      | windowEnd rightClosingAbsent rightAtEnd =>
          exact False.elim (Nat.not_lt_of_ge rightAtEnd leftInside)
      | memberAtBoundary rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryPresent =>
          exact False.elim (leftBoundaryAbsent rightBoundaryPresent)
      | recoveryRejected rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryAbsent rightRecovery =>
          exact False.elim
            (contractMemberRecoveryExactOutcomeSpec.successRejectDisjoint
              rightRecovery ⟨_, _, leftRecovery⟩)
      | laterDirect rightClosingAbsent rightInside rightMember rightProgress
          rightTail =>
          exact False.elim
            (leftMemberRejected.disjointOrdinary ⟨_, _, rightMember⟩)
      | laterRecovered rightClosingAbsent rightInside rightMemberRejected
          rightBoundaryAbsent rightRecovery rightTail =>
          have afterRecoveryEq :=
            contractMemberRecoveryExactOutcomeSpec.successOutputUnique
              leftRecovery rightRecovery
          subst afterRecoveryEq
          exact inductionHypothesis rightTail

/-- Exact derive-aware members lift through the complete body-tail loop. -/
theorem contractMemberTailExactOutcomeSpecOfMember
    (memberOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberOrdinaryParses ContractMemberRejects) :
    ExactDeterministicOutcomeSpec ContractMemberTailOrdinaryOutcomeParses
      ContractMemberTailRejects where
  toDeterministicOutcomeSpec := contractMemberTailDeterministicOutcomeSpec
  successValueUnique :=
    ContractMemberTailOrdinaryOutcomeParses.value_unique_of_member
      memberOutcomes
  rejectOutputUnique :=
    ContractMemberTailRejects.output_unique_of_member memberOutcomes

/-- Exact member outcomes make a complete contract body fix its body value. -/
theorem ContractBodyOrdinaryOutcomeParses.value_unique_of_member
    (memberOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberOrdinaryParses ContractMemberRejects)
    {input : Remainder}
    {left right : SourceSpan × List Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractBodyOrdinaryOutcomeParses input left afterLeft)
    (rightParsed : ContractBodyOrdinaryOutcomeParses input right afterRight) :
    left = right := by
  rcases left with ⟨leftSpan, leftMembers⟩
  rcases right with ⟨rightSpan, rightMembers⟩
  cases leftParsed with
  | parsed leftOpening leftClosing leftOpeningToken leftTail =>
      cases rightParsed with
      | parsed rightOpening rightClosing rightOpeningToken rightTail =>
          rcases leftOpeningToken.result_unique rightOpeningToken with
            ⟨openingEq, afterOpeningEq⟩
          subst openingEq
          subst afterOpeningEq
          rcases rightTail.result_unique_of_member memberOutcomes leftTail with
            ⟨membersEq, closingEq, outputEq⟩
          subst membersEq
          subst closingEq
          rfl

/-- Exact member outcomes fix complete contract-body rejection endpoints. -/
theorem ContractBodyRejects.output_unique_of_member
    (memberOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberOrdinaryParses ContractMemberRejects)
    {input left right : Remainder}
    (leftRejected : ContractBodyRejects input left)
    (rightRejected : ContractBodyRejects input right) : left = right := by
  cases leftRejected with
  | openingMissing leftOpeningAbsent =>
      cases rightRejected with
      | openingMissing => rfl
      | tailRejected rightSpan rightOpening rightTail =>
          exact False.elim
            (contractBody_absent_conflicts_exact leftOpeningAbsent
              rightOpening)
  | tailRejected leftSpan leftOpening leftTail =>
      cases rightRejected with
      | openingMissing rightOpeningAbsent =>
          exact False.elim
            (contractBody_absent_conflicts_exact rightOpeningAbsent
              leftOpening)
      | tailRejected rightSpan rightOpening rightTail =>
          have afterOpeningEq := leftOpening.output_unique rightOpening
          subst afterOpeningEq
          exact leftTail.output_unique_of_member memberOutcomes rightTail

/-- Exact derive-aware member outcomes lift through a complete contract body. -/
theorem contractBodyExactOutcomeSpecOfMember
    (memberOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberOrdinaryParses ContractMemberRejects) :
    ExactDeterministicOutcomeSpec ContractBodyOrdinaryOutcomeParses
      ContractBodyRejects where
  toDeterministicOutcomeSpec := contractBodyDeterministicOutcomeSpec
  successValueUnique :=
    ContractBodyOrdinaryOutcomeParses.value_unique_of_member memberOutcomes
  rejectOutputUnique :=
    ContractBodyRejects.output_unique_of_member memberOutcomes

/-- Exact attribute-free core outcomes supply exact derive-aware members and
therefore exact recovery-aware contract bodies. -/
theorem contractBodyExactOutcomeSpecOfCore
    (coreOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberCoreOrdinaryParses ContractMemberCoreRejects) :
    ExactDeterministicOutcomeSpec ContractBodyOrdinaryOutcomeParses
      ContractBodyRejects :=
  contractBodyExactOutcomeSpecOfMember
    (contractMemberExactOutcomeSpecOfCore coreOutcomes)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractDeclarationOutcomeProperties
/-! Deterministic exact ordinary outcomes for contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem contractBody_output_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftMembers rightMembers : List Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractBodyOrdinaryParses input leftSpan leftMembers
      afterLeft)
    (rightParsed : ContractBodyOrdinaryParses input rightSpan rightMembers
      afterRight) : afterLeft = afterRight :=
  contractBodyDeterministicOutcomeSpec.successOutputUnique
    (left := (leftSpan, leftMembers))
    (right := (rightSpan, rightMembers)) leftParsed rightParsed

private theorem contractBody_reject_disjoint
    {input rejected : Remainder} (rejection : ContractBodyRejects input rejected) :
    ¬ ∃ span members output,
      ContractBodyOrdinaryParses input span members output := by
  rintro ⟨span, members, output, parsed⟩
  exact contractBodyDeterministicOutcomeSpec.successRejectDisjoint rejection
    ⟨(span, members), output, parsed⟩

/-- Broad contract-declaration success has one final remainder. -/
theorem ContractDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ContractDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractDeclOrdinaryParses input left afterLeft)
    (rightParsed : ContractDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftName leftGenerics leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightName rightGenerics rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          cases afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          cases afterNameEq
          have afterGenericsEq := leftGenerics.output_unique rightGenerics
          cases afterGenericsEq
          exact contractBody_output_unique leftBody rightBody

/-- Exact contract-declaration rejection excludes every broad success. -/
theorem ContractDeclRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : ContractDeclRejects input rejected) :
    ¬ ∃ declaration output,
      ContractDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulName
        successfulGenerics successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | nameRejected rejectedMarkerSpan rejectedMarker nameRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | genericsRejected rejectedMarkerSpan rejectedMarker rejectedName
            genericsRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          cases afterNameEq
          exact optionalGenericParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint genericsRejected
              ⟨_, _, successfulGenerics⟩
      | bodyRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedGenerics bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          cases afterNameEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          cases afterGenericsEq
          exact contractBody_reject_disjoint bodyRejected
            ⟨_, _, _, successfulBody⟩

/-- Contract declarations have deterministic and exclusive broad outcomes. -/
theorem contractDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ContractDeclOrdinaryParses ContractDeclRejects where
  successOutputUnique := ContractDeclOrdinaryParses.output_unique
  successRejectDisjoint := ContractDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractDeclarationExactnessProperties
/-! Exactness transport through complete contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem contractDecl_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- An exact contract-body outcome makes a declaration fix its complete AST. -/
theorem ContractDeclOrdinaryParses.value_unique_of_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ContractBodyOrdinaryOutcomeParses ContractBodyRejects)
    {input : Remainder} {left right : Syntax.ContractDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractDeclOrdinaryParses input left afterLeft)
    (rightParsed : ContractDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftName leftGenerics leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightName rightGenerics rightBody =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases optionalGenericParametersExactOutcomeSpec.successResultUnique
              leftGenerics rightGenerics with
            ⟨genericsEq, afterGenericsEq⟩
          subst genericsEq
          subst afterGenericsEq
          have bodyEq := bodyOutcomes.successValueUnique
            (show ContractBodyOrdinaryOutcomeParses _ (_, _) _ from leftBody)
            (show ContractBodyOrdinaryOutcomeParses _ (_, _) _ from rightBody)
          cases bodyEq
          rfl

/-- Under an exact body contract, declaration success fixes its AST and final
remainder. -/
theorem ContractDeclOrdinaryParses.result_unique_of_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ContractBodyOrdinaryOutcomeParses ContractBodyRejects)
    {input : Remainder} {left right : Syntax.ContractDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractDeclOrdinaryParses input left afterLeft)
    (rightParsed : ContractDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_body bodyOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Under an exact body contract, declaration rejection has one endpoint. -/
theorem ContractDeclRejects.output_unique_of_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ContractBodyOrdinaryOutcomeParses ContractBodyRejects)
    {input left right : Remainder}
    (leftRejected : ContractDeclRejects input left)
    (rightRejected : ContractDeclRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 10) [contractDecl_absent_conflicts_exact,
      ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      optionalGenericParametersExactOutcomeSpec.successOutputUnique,
      optionalGenericParametersExactOutcomeSpec.successRejectDisjoint,
      optionalGenericParametersExactOutcomeSpec.rejectOutputUnique,
      bodyOutcomes.rejectOutputUnique]

/-- An exact complete contract body lifts to exact declaration outcomes. -/
theorem contractDeclExactOutcomeSpecOfBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      ContractBodyOrdinaryOutcomeParses ContractBodyRejects) :
    ExactDeterministicOutcomeSpec ContractDeclOrdinaryParses
      ContractDeclRejects where
  toDeterministicOutcomeSpec := contractDeclDeterministicOutcomeSpec
  successValueUnique :=
    ContractDeclOrdinaryParses.value_unique_of_body bodyOutcomes
  rejectOutputUnique := ContractDeclRejects.output_unique_of_body bodyOutcomes

/-- Exact attribute-free member outcomes lift through derive attachment,
recovery, the body loop, and the complete contract declaration. -/
theorem contractDeclExactOutcomeSpecOfCore
    (coreOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberCoreOrdinaryParses ContractMemberCoreRejects) :
    ExactDeterministicOutcomeSpec ContractDeclOrdinaryParses
      ContractDeclRejects :=
  contractDeclExactOutcomeSpecOfBody
    (contractBodyExactOutcomeSpecOfCore coreOutcomes)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImplMethodOutcomeProperties
/-! Deterministic exact ordinary outcomes for implementation methods. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary implementation-method success has one final remainder. -/
theorem ImplMethodOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ImplMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplMethodOrdinaryParses input left afterLeft)
    (rightParsed : ImplMethodOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftDeclaration =>
      cases rightParsed with
      | parsed rightDeclaration =>
          exact leftDeclaration.output_unique rightDeclaration

/-- Nested declaration rejection excludes every ordinary method success. -/
theorem ImplMethodRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ImplMethodRejects input rejected) :
    ¬ ∃ method output, ImplMethodOrdinaryParses input method output := by
  rintro ⟨method, output, successful⟩
  cases rejection with
  | declarationRejected declarationRejected =>
      cases successful with
      | parsed declarationParsed =>
          exact functionDeclDeterministicOutcomeSpec.successRejectDisjoint
            declarationRejected ⟨_, _, declarationParsed⟩

/-- Implementation methods have deterministic and exclusive ordinary
outcomes. -/
theorem implMethodDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ImplMethodOrdinaryParses ImplMethodRejects where
  successOutputUnique := ImplMethodOrdinaryParses.output_unique
  successRejectDisjoint := ImplMethodRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImplBodyOutcomeProperties
/-! Deterministic exact ordinary outcomes for prioritized implementation bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImplDeclarationOutcomeProperties
/-! Deterministic exact ordinary outcomes for implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem implBody_output_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftMethods rightMethods : List Syntax.ImplMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplBodyOrdinaryParses input leftSpan leftMethods afterLeft)
    (rightParsed : ImplBodyOrdinaryParses input rightSpan rightMethods
      afterRight) : afterLeft = afterRight :=
  implBodyDeterministicOutcomeSpec.successOutputUnique
    (left := (leftSpan, leftMethods))
    (right := (rightSpan, rightMethods)) leftParsed rightParsed

private theorem implBody_reject_disjoint
    {input rejected : Remainder} (rejection : ImplBodyRejects input rejected) :
    ¬ ∃ span methods output,
      ImplBodyOrdinaryParses input span methods output := by
  rintro ⟨span, methods, output, parsed⟩
  exact implBodyDeterministicOutcomeSpec.successRejectDisjoint rejection
    ⟨(span, methods), output, parsed⟩

/-- Ordinary implementation-declaration success has one final remainder. -/
theorem ImplDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ImplDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplDeclOrdinaryParses input left afterLeft)
    (rightParsed : ImplDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftDefault leftMarkerSpan leftMarker leftGenerics leftName
        leftArguments leftWhere leftBody =>
      cases rightParsed with
      | parsed rightDefault rightMarkerSpan rightMarker rightGenerics
            rightName rightArguments rightWhere rightBody =>
          have afterDefaultEq := leftDefault.output_unique rightDefault
          subst afterDefaultEq
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterGenericsEq := leftGenerics.output_unique rightGenerics
          subst afterGenericsEq
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          have afterArgumentsEq := leftArguments.output_unique rightArguments
          subst afterArgumentsEq
          have afterWhereEq := leftWhere.output_unique rightWhere
          subst afterWhereEq
          exact implBody_output_unique leftBody rightBody

/-- Exact implementation-declaration rejection excludes every ordinary
success. -/
theorem ImplDeclRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : ImplDeclRejects input rejected) :
    ¬ ∃ declaration output,
      ImplDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulDefault successfulMarkerSpan successfulMarker
        successfulGenerics successfulName successfulArguments successfulWhere
        successfulBody =>
      cases rejection with
      | markerMissing rejectedDefault markerAbsent =>
          have afterDefaultEq := rejectedDefault.output_unique
            successfulDefault
          subst afterDefaultEq
          exact absent_conflicts_exact markerAbsent successfulMarker
      | genericsRejected rejectedDefault rejectedMarkerSpan rejectedMarker
            genericsRejected =>
          have afterDefaultEq := rejectedDefault.output_unique
            successfulDefault
          subst afterDefaultEq
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact optionalGenericParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint genericsRejected
              ⟨_, _, successfulGenerics⟩
      | nameRejected rejectedDefault rejectedMarkerSpan rejectedMarker
            rejectedGenerics nameRejected =>
          have afterDefaultEq := rejectedDefault.output_unique
            successfulDefault
          subst afterDefaultEq
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | argumentsRejected rejectedDefault rejectedMarkerSpan rejectedMarker
            rejectedGenerics rejectedName argumentsRejected =>
          have afterDefaultEq := rejectedDefault.output_unique
            successfulDefault
          subst afterDefaultEq
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          exact implHeadArgumentsDeterministicOutcomeSpec
            |>.successRejectDisjoint argumentsRejected
              ⟨_, _, successfulArguments⟩
      | whereRejected rejectedDefault rejectedMarkerSpan rejectedMarker
            rejectedGenerics rejectedName rejectedArguments whereRejected =>
          have afterDefaultEq := rejectedDefault.output_unique
            successfulDefault
          subst afterDefaultEq
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterArgumentsEq := rejectedArguments.output_unique
            successfulArguments
          subst afterArgumentsEq
          exact optionalWhereClauseDeterministicOutcomeSpec
            |>.successRejectDisjoint whereRejected ⟨_, _, successfulWhere⟩
      | bodyRejected rejectedDefault rejectedMarkerSpan rejectedMarker
            rejectedGenerics rejectedName rejectedArguments rejectedWhere
            bodyRejected =>
          have afterDefaultEq := rejectedDefault.output_unique
            successfulDefault
          subst afterDefaultEq
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterArgumentsEq := rejectedArguments.output_unique
            successfulArguments
          subst afterArgumentsEq
          have afterWhereEq := rejectedWhere.output_unique successfulWhere
          subst afterWhereEq
          exact implBody_reject_disjoint bodyRejected
            ⟨_, _, _, successfulBody⟩

/-- Implementation declarations have deterministic and exclusive broad
ordinary outcomes. -/
theorem implDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ImplDeclOrdinaryParses ImplDeclRejects where
  successOutputUnique := ImplDeclOrdinaryParses.output_unique
  successRejectDisjoint := ImplDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end
