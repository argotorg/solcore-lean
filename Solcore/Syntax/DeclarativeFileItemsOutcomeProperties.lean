import Solcore.Syntax.DeclarativeFileItemsOutcomeGrammar
import Solcore.Syntax.DeclarativeTopItemOutcomeProperties
import Solcore.Syntax.DeclarativeTopItemRecoveryOutcomeProperties

/-! Deterministic broad outcomes for the recovery-aware file-item loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Preserved carrier and window evidence makes the file-loop rewind exact. -/
theorem TopItemRejectsWithPreservedWindow.exists_rewind_eq
    {input : Remainder}
    (rejected : TopItemRejectsWithPreservedWindow input) :
    ∃ failed, TopItemRejects input failed ∧
      { failed with cursor := input.cursor } = input := by
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  refine ⟨failed, rejection, ?_⟩
  cases input
  cases failed
  simp_all

/-- A window-preserving top-item rejection excludes every broad top-item
success from the same input. -/
theorem TopItemRejectsWithPreservedWindow.disjointOrdinary
    {input : Remainder}
    (rejected : TopItemRejectsWithPreservedWindow input) :
    ¬ ∃ item output, TopItemOrdinaryParses input item output := by
  rintro ⟨item, output, parsed⟩
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  exact topItemDeterministicOutcomeSpec.successRejectDisjoint rejection
    ⟨_, _, parsed⟩

/-- A forward file-item suffix has one final remainder. -/
theorem FileItemsOrdinaryParses.output_unique
    {input : Remainder} {leftItems rightItems : List Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : FileItemsOrdinaryParses input leftItems afterLeft)
    (rightParsed : FileItemsOrdinaryParses input rightItems afterRight) :
    afterLeft = afterRight := by
  induction leftParsed generalizing rightItems afterRight with
  | done leftAtEnd =>
      cases rightParsed with
      | done => rfl
      | direct rightInside rightItem rightProgress rightTail =>
          exact False.elim
            (Nat.not_lt_of_ge leftAtEnd rightInside)
      | boundaryStop rightInside rightRejected rightBoundary =>
          exact False.elim
            (Nat.not_lt_of_ge leftAtEnd rightInside)
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          exact False.elim
            (Nat.not_lt_of_ge leftAtEnd rightInside)
  | direct leftInside leftItem leftProgress leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAtEnd =>
          exact False.elim
            (Nat.not_lt_of_ge rightAtEnd leftInside)
      | direct rightInside rightItem rightProgress rightTail =>
          have afterItemEq :=
            topItemDeterministicOutcomeSpec.successOutputUnique
              leftItem rightItem
          cases afterItemEq
          exact inductionHypothesis rightTail
      | boundaryStop rightInside rightRejected rightBoundary =>
          exact False.elim
            (rightRejected.disjointOrdinary ⟨_, _, leftItem⟩)
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          exact False.elim
            (rightRejected.disjointOrdinary ⟨_, _, leftItem⟩)
  | boundaryStop leftInside leftRejected leftBoundary =>
      cases rightParsed with
      | done rightAtEnd =>
          exact False.elim
            (Nat.not_lt_of_ge rightAtEnd leftInside)
      | direct rightInside rightItem rightProgress rightTail =>
          exact False.elim
            (leftRejected.disjointOrdinary ⟨_, _, rightItem⟩)
      | boundaryStop => rfl
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          exact False.elim (rightBoundaryAbsent leftBoundary)
  | recovered leftInside leftRejected leftBoundaryAbsent leftRecovery
        leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAtEnd =>
          exact False.elim
            (Nat.not_lt_of_ge rightAtEnd leftInside)
      | direct rightInside rightItem rightProgress rightTail =>
          exact False.elim
            (leftRejected.disjointOrdinary ⟨_, _, rightItem⟩)
      | boundaryStop rightInside rightRejected rightBoundary =>
          exact False.elim (leftBoundaryAbsent rightBoundary)
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          have afterRecoveryEq :=
            topItemRecoveryDeterministicOutcomeSpec.successOutputUnique
              leftRecovery rightRecovery
          cases afterRecoveryEq
          exact inductionHypothesis rightTail

/-- Exact file-loop rejection excludes every successful forward suffix. -/
theorem FileItemsRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : FileItemsRejects input rejected) :
    ¬ ∃ items output, FileItemsOrdinaryParses input items output := by
  induction rejection with
  | recoveryRejected rejectedInside rejectedItem rejectedBoundaryAbsent
        rejectedRecovery =>
      rintro ⟨items, output, parsed⟩
      cases parsed with
      | done successfulAtEnd =>
          exact Nat.not_lt_of_ge successfulAtEnd rejectedInside
      | direct successfulInside successfulItem successfulProgress
            successfulTail =>
          exact rejectedItem.disjointOrdinary ⟨_, _, successfulItem⟩
      | boundaryStop successfulInside successfulRejected
            successfulBoundary =>
          exact rejectedBoundaryAbsent successfulBoundary
      | recovered successfulInside successfulRejected
            successfulBoundaryAbsent successfulRecovery successfulTail =>
          exact topItemRecoveryDeterministicOutcomeSpec
            |>.successRejectDisjoint rejectedRecovery
              ⟨_, _, successfulRecovery⟩
  | laterDirect rejectedInside rejectedItem rejectedProgress tailRejected
        inductionHypothesis =>
      rintro ⟨items, output, parsed⟩
      cases parsed with
      | done successfulAtEnd =>
          exact Nat.not_lt_of_ge successfulAtEnd rejectedInside
      | direct successfulInside successfulItem successfulProgress
            successfulTail =>
          have afterItemEq :=
            topItemDeterministicOutcomeSpec.successOutputUnique
              rejectedItem successfulItem
          cases afterItemEq
          exact inductionHypothesis ⟨_, _, successfulTail⟩
      | boundaryStop successfulInside successfulRejected
            successfulBoundary =>
          exact successfulRejected.disjointOrdinary ⟨_, _, rejectedItem⟩
      | recovered successfulInside successfulRejected
            successfulBoundaryAbsent successfulRecovery successfulTail =>
          exact successfulRejected.disjointOrdinary ⟨_, _, rejectedItem⟩
  | laterRecovered rejectedInside rejectedItem rejectedBoundaryAbsent
        rejectedRecovery tailRejected inductionHypothesis =>
      rintro ⟨items, output, parsed⟩
      cases parsed with
      | done successfulAtEnd =>
          exact Nat.not_lt_of_ge successfulAtEnd rejectedInside
      | direct successfulInside successfulItem successfulProgress
            successfulTail =>
          exact rejectedItem.disjointOrdinary ⟨_, _, successfulItem⟩
      | boundaryStop successfulInside successfulRejected
            successfulBoundary =>
          exact rejectedBoundaryAbsent successfulBoundary
      | recovered successfulInside successfulRejected
            successfulBoundaryAbsent successfulRecovery successfulTail =>
          have afterRecoveryEq :=
            topItemRecoveryDeterministicOutcomeSpec.successOutputUnique
              rejectedRecovery successfulRecovery
          cases afterRecoveryEq
          exact inductionHypothesis ⟨_, _, successfulTail⟩

/-- File-item suffixes have deterministic and exclusive broad outcomes. -/
theorem fileItemsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec FileItemsOrdinaryParses FileItemsRejects where
  successOutputUnique := FileItemsOrdinaryParses.output_unique
  successRejectDisjoint := FileItemsRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
