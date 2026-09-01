import Solcore.Syntax.DeclarativeCorePatternRecoveryOutcomeGrammar

/-! Functionality and outcome exclusion for Core pattern recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- Every pattern recovery stop preserves its complete remainder. -/
theorem PatternRecoveryStops.output_eq {input stopped : Remainder}
    (stops : PatternRecoveryStops input stopped) : stopped = input := by
  cases stops <;> rfl

/-- A pattern recovery scan has functional output from one remainder. -/
theorem PatternRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.Pattern} {afterLeft afterRight : Remainder},
      PatternRecoveryScanParses first leftLast input left afterLeft →
      PatternRecoveryScanParses first rightLast input right afterRight →
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

/-- Complete ordinary pattern recovery has functional output. -/
theorem PatternRecoveryParses.output_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternRecoveryParses input left afterLeft)
    (rightParsed : PatternRecoveryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Every complete pattern recovery rejection is non-consuming. -/
theorem PatternRecoveryRejects.output_eq {input rejected : Remainder}
    (rejection : PatternRecoveryRejects input rejected) : rejected = input := by
  cases rejection <;> rfl

/-- A present first token excludes complete pattern recovery rejection. -/
theorem PatternRecoveryRejects.disjointParses
    {input rejected : Remainder}
    (rejection : PatternRecoveryRejects input rejected) :
    ¬ ∃ pattern output, PatternRecoveryParses input pattern output := by
  rintro ⟨pattern, output, parsed⟩
  cases parsed with
  | recovered current scan =>
      cases rejection with
      | windowEnd atEnd =>
          exact False.elim (Nat.not_lt_of_ge atEnd current.1)
      | missingToken inside missing =>
          rw [current.2] at missing
          contradiction

/-- Deterministic ordinary outcome contract for complete pattern recovery. -/
theorem patternRecoveryDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PatternRecoveryParses PatternRecoveryRejects where
  successOutputUnique := PatternRecoveryParses.output_unique
  successRejectDisjoint := PatternRecoveryRejects.disjointParses

end Solcore.Syntax.DeclarativeGrammar
