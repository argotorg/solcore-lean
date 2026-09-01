import Solcore.Syntax.DeclarativeCoreExpressionAtomRecoveryGrammar

/-! Functionality and outcome exclusion for Core atom recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- Every scan stop preserves its complete declarative remainder. -/
theorem ExpressionAtomRecoveryStops.output_eq
    {input stopped : Remainder}
    (stops : ExpressionAtomRecoveryStops input stopped) : stopped = input := by
  cases stops <;> rfl

/-- An atom recovery scan has functional output from one current remainder. -/
theorem ExpressionAtomRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.Expr} {afterLeft afterRight : Remainder},
      ExpressionAtomRecoveryScanParses first leftLast input left afterLeft →
      ExpressionAtomRecoveryScanParses first rightLast input right afterRight →
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

/-- Complete ordinary atom recovery has functional output. -/
theorem ExpressionAtomRecoveryParses.output_unique
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomRecoveryParses input left afterLeft)
    (rightParsed : ExpressionAtomRecoveryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Every complete recovery rejection is non-consuming. -/
theorem ExpressionAtomRecoveryRejects.output_eq
    {input rejected : Remainder}
    (rejection : ExpressionAtomRecoveryRejects input rejected) :
    rejected = input := by
  cases rejection <;> rfl

/-- A present first token excludes complete recovery rejection. -/
theorem ExpressionAtomRecoveryRejects.disjointParses
    {input rejected : Remainder}
    (rejection : ExpressionAtomRecoveryRejects input rejected) :
    ¬ ∃ expression output, ExpressionAtomRecoveryParses input expression output := by
  rintro ⟨expression, output, parsed⟩
  cases parsed with
  | recovered current scan =>
      cases rejection with
      | windowEnd atEnd => exact False.elim (Nat.not_lt_of_ge atEnd current.1)
      | missingToken inside missing =>
          rw [current.2] at missing
          contradiction

/-- Deterministic ordinary outcome contract for complete atom recovery. -/
theorem expressionAtomRecoveryDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ExpressionAtomRecoveryParses
      ExpressionAtomRecoveryRejects where
  successOutputUnique := ExpressionAtomRecoveryParses.output_unique
  successRejectDisjoint := ExpressionAtomRecoveryRejects.disjointParses

end Solcore.Syntax.DeclarativeGrammar
