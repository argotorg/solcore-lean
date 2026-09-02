import Solcore.Syntax.DeclarativeContractBodyOutcomeProperties
import Solcore.Syntax.DeclarativeContractMemberRecoveryExactnessProperties
import Solcore.Syntax.DeclarativeContractMemberWithAttributeExactnessProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

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
