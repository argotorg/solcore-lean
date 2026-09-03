import Solcore.Syntax.DeclarativeFileItemsOutcomeProperties
import Solcore.Syntax.DeclarativeTopItemRecoveryExactnessProperties

/-! Exact recovery-aware file-item outcomes from successful top-item values. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The file loop's rejecting endpoint is unconditional: raw top-item failures
are rewound, and recovery rejection always retains its original input. -/
theorem FileItemsRejects.output_unique {input left right : Remainder}
    (leftRejected : FileItemsRejects input left)
    (rightRejected : FileItemsRejects input right) : left = right := by
  induction leftRejected generalizing right with
  | recoveryRejected leftInside leftItem leftBoundary leftRecovery =>
      cases rightRejected with
      | recoveryRejected rightInside rightItem rightBoundary rightRecovery =>
          exact leftRecovery.output_unique rightRecovery
      | laterDirect rightInside rightItem rightProgress rightTail =>
          exact False.elim (leftItem.disjointOrdinary ⟨_, _, rightItem⟩)
      | laterRecovered rightInside rightItem rightBoundary rightRecovery
            rightTail =>
          exact False.elim
            (leftRecovery.disjointParses ⟨_, _, rightRecovery⟩)
  | laterDirect leftInside leftItem leftProgress leftTail ih =>
      cases rightRejected with
      | recoveryRejected rightInside rightItem rightBoundary rightRecovery =>
          exact False.elim (rightItem.disjointOrdinary ⟨_, _, leftItem⟩)
      | laterDirect rightInside rightItem rightProgress rightTail =>
          have inputEq := topItemDeterministicOutcomeSpec.successOutputUnique
            leftItem rightItem
          subst inputEq
          exact ih rightTail
      | laterRecovered rightInside rightItem rightBoundary rightRecovery
            rightTail =>
          exact False.elim (rightItem.disjointOrdinary ⟨_, _, leftItem⟩)
  | laterRecovered leftInside leftItem leftBoundary leftRecovery leftTail ih =>
      cases rightRejected with
      | recoveryRejected rightInside rightItem rightBoundary rightRecovery =>
          exact False.elim
            (rightRecovery.disjointParses ⟨_, _, leftRecovery⟩)
      | laterDirect rightInside rightItem rightProgress rightTail =>
          exact False.elim (leftItem.disjointOrdinary ⟨_, _, rightItem⟩)
      | laterRecovered rightInside rightItem rightBoundary rightRecovery
            rightTail =>
          have inputEq := leftRecovery.output_unique rightRecovery
          subst inputEq
          exact ih rightTail

/-- Unique successful top-item ASTs make the recovery-aware file loop fix its
complete forward item list, preserving boundary-stop priority. -/
theorem FileItemsOrdinaryParses.value_unique_of_topItem
    (itemValues : ∀ {input left right afterLeft afterRight},
      TopItemOrdinaryParses input left afterLeft →
      TopItemOrdinaryParses input right afterRight → left = right)
    {input : Remainder} {leftItems rightItems : List Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : FileItemsOrdinaryParses input leftItems afterLeft)
    (rightParsed : FileItemsOrdinaryParses input rightItems afterRight) :
    leftItems = rightItems := by
  induction leftParsed generalizing rightItems afterRight with
  | done leftAtEnd =>
      cases rightParsed with
      | done => rfl
      | direct rightInside rightItem rightProgress rightTail =>
          exact False.elim (Nat.not_lt_of_ge leftAtEnd rightInside)
      | boundaryStop rightInside rightRejected rightBoundary =>
          exact False.elim (Nat.not_lt_of_ge leftAtEnd rightInside)
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          exact False.elim (Nat.not_lt_of_ge leftAtEnd rightInside)
  | direct leftInside leftItem leftProgress leftTail ih =>
      cases rightParsed with
      | done rightAtEnd =>
          exact False.elim (Nat.not_lt_of_ge rightAtEnd leftInside)
      | direct rightInside rightItem rightProgress rightTail =>
          have itemEq := itemValues leftItem rightItem
          subst itemEq
          have inputEq := topItemDeterministicOutcomeSpec.successOutputUnique
            leftItem rightItem
          subst inputEq
          have tailEq := ih rightTail
          subst tailEq
          rfl
      | boundaryStop rightInside rightRejected rightBoundary =>
          exact False.elim (rightRejected.disjointOrdinary ⟨_, _, leftItem⟩)
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          exact False.elim (rightRejected.disjointOrdinary ⟨_, _, leftItem⟩)
  | boundaryStop leftInside leftRejected leftBoundary =>
      cases rightParsed with
      | done rightAtEnd =>
          exact False.elim (Nat.not_lt_of_ge rightAtEnd leftInside)
      | direct rightInside rightItem rightProgress rightTail =>
          exact False.elim (leftRejected.disjointOrdinary ⟨_, _, rightItem⟩)
      | boundaryStop => rfl
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          exact False.elim (rightBoundaryAbsent leftBoundary)
  | recovered leftInside leftRejected leftBoundaryAbsent leftRecovery
        leftTail ih =>
      cases rightParsed with
      | done rightAtEnd =>
          exact False.elim (Nat.not_lt_of_ge rightAtEnd leftInside)
      | direct rightInside rightItem rightProgress rightTail =>
          exact False.elim (leftRejected.disjointOrdinary ⟨_, _, rightItem⟩)
      | boundaryStop rightInside rightRejected rightBoundary =>
          exact False.elim (leftBoundaryAbsent rightBoundary)
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          rcases leftRecovery.result_unique rightRecovery with
            ⟨itemEq, inputEq⟩
          subst itemEq
          subst inputEq
          have tailEq := ih rightTail
          subst tailEq
          rfl

/-- Unique successful top items fix the whole file-item list and remainder. -/
theorem FileItemsOrdinaryParses.result_unique_of_topItem
    (itemValues : ∀ {input left right afterLeft afterRight},
      TopItemOrdinaryParses input left afterLeft →
      TopItemOrdinaryParses input right afterRight → left = right)
    {input : Remainder} {leftItems rightItems : List Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : FileItemsOrdinaryParses input leftItems afterLeft)
    (rightParsed : FileItemsOrdinaryParses input rightItems afterRight) :
    leftItems = rightItems ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_topItem itemValues rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Top-item success-value uniqueness alone supplies exact file-loop outcomes;
raw top-item rejection endpoint uniqueness is not required. -/
theorem fileItemsExactOutcomeSpecOfTopItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      TopItemOrdinaryParses input left afterLeft →
      TopItemOrdinaryParses input right afterRight → left = right) :
    ExactDeterministicOutcomeSpec FileItemsOrdinaryParses FileItemsRejects where
  toDeterministicOutcomeSpec := fileItemsDeterministicOutcomeSpec
  successValueUnique := FileItemsOrdinaryParses.value_unique_of_topItem itemValues
  rejectOutputUnique := FileItemsRejects.output_unique

/-- An exact top-item contract supplies complete exact file-loop outcomes. -/
theorem fileItemsExactOutcomeSpecOfTopItem
    (itemOutcomes : ExactDeterministicOutcomeSpec TopItemOrdinaryParses
      TopItemRejects) :
    ExactDeterministicOutcomeSpec FileItemsOrdinaryParses FileItemsRejects :=
  fileItemsExactOutcomeSpecOfTopItemValues itemOutcomes.successValueUnique

end Solcore.Syntax.DeclarativeGrammar
