import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.DeclarativeTopItemRecoveryOutcomeGrammar

/-! Functionality and outcome exclusion for top-item recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- A top-item recovery scan has one final remainder. -/
theorem TopItemRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.TopItem} {afterLeft afterRight : Remainder},
      TopItemRecoveryScanParses first leftLast input left afterLeft →
      TopItemRecoveryScanParses first rightLast input right afterRight →
      afterLeft = afterRight := by
  intro first leftLast rightLast input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing rightLast right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- Complete ordinary top-item recovery has one final remainder. -/
theorem TopItemRecoveryParses.output_unique
    {input : Remainder} {left right : Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : TopItemRecoveryParses input left afterLeft)
    (rightParsed : TopItemRecoveryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Every top-item recovery rejection is non-consuming. -/
theorem TopItemRecoveryRejects.output_eq
    {input rejected : Remainder}
    (rejection : TopItemRecoveryRejects input rejected) :
    rejected = input := by
  cases rejection <;> rfl

/-- An unavailable mandatory first token excludes every recovery success. -/
theorem TopItemRecoveryRejects.disjointParses
    {input rejected : Remainder}
    (rejection : TopItemRecoveryRejects input rejected) :
    ¬ ∃ item output, TopItemRecoveryParses input item output := by
  rintro ⟨item, output, parsed⟩
  cases parsed with
  | recovered current scan =>
      cases rejection with
      | windowEnd atEnd => exact Nat.not_lt_of_ge atEnd current.1
      | missingToken inside missing =>
          rw [current.2] at missing
          contradiction

/-- Deterministic ordinary outcome contract for top-item recovery. -/
theorem topItemRecoveryDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TopItemRecoveryParses
      TopItemRecoveryRejects where
  successOutputUnique := TopItemRecoveryParses.output_unique
  successRejectDisjoint := TopItemRecoveryRejects.disjointParses

end Solcore.Syntax.DeclarativeGrammar
