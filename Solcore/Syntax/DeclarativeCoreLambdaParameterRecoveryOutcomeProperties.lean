import Solcore.Syntax.DeclarativeCoreLambdaParameterRecoveryOutcomeGrammar

/-! Deterministic ordinary outcomes of parameter recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- The recursive recovery scan has one deterministic remainder. -/
theorem FunctionParameterRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.FunctionParameter}
      {afterLeft afterRight : Remainder},
      FunctionParameterRecoveryScanParses first leftLast input left afterLeft →
      FunctionParameterRecoveryScanParses first rightLast input right afterRight →
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

/-- Complete function-parameter recovery has one deterministic remainder. -/
theorem FunctionParameterRecoveryParses.output_unique
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterRecoveryParses input left afterLeft)
    (rightParsed : FunctionParameterRecoveryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Lambda retagging preserves the function recovery's unique remainder. -/
theorem LambdaParameterRecoveryParses.output_unique
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterRecoveryParses input left afterLeft)
    (rightParsed : LambdaParameterRecoveryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftRecovery =>
      cases rightParsed with
      | recovered rightRecovery =>
          exact leftRecovery.output_unique rightRecovery

/-- Every unavailable-first-token rejection is non-consuming. -/
theorem FunctionParameterRecoveryRejects.output_eq
    {input rejected : Remainder}
    (rejection : FunctionParameterRecoveryRejects input rejected) :
    rejected = input := by
  cases rejection <;> rfl

/-- A present first token excludes recovery rejection. -/
theorem FunctionParameterRecoveryRejects.disjointParses
    {input rejected : Remainder}
    (rejection : FunctionParameterRecoveryRejects input rejected) :
    ¬ ∃ parameter output,
      FunctionParameterRecoveryParses input parameter output := by
  rintro ⟨parameter, output, parsed⟩
  cases parsed with
  | recovered current scan =>
      cases rejection with
      | windowEnd atEnd => exact Nat.not_lt_of_ge atEnd current.1
      | missingToken inside missing =>
          rw [current.2] at missing
          contradiction

/-- The same first-token exclusion applies after lambda retagging. -/
theorem FunctionParameterRecoveryRejects.disjointLambdaParses
    {input rejected : Remainder}
    (rejection : FunctionParameterRecoveryRejects input rejected) :
    ¬ ∃ parameter output,
      LambdaParameterRecoveryParses input parameter output := by
  rintro ⟨parameter, output, parsed⟩
  cases parsed with
  | recovered recovered =>
      exact rejection.disjointParses ⟨_, _, recovered⟩

/-- Deterministic ordinary function-parameter recovery outcome. -/
theorem functionParameterRecoveryDeterministicOutcomeSpec :
    DeterministicOutcomeSpec FunctionParameterRecoveryParses
      FunctionParameterRecoveryRejects where
  successOutputUnique := FunctionParameterRecoveryParses.output_unique
  successRejectDisjoint := FunctionParameterRecoveryRejects.disjointParses

/-- Deterministic ordinary lambda-parameter recovery outcome. -/
theorem lambdaParameterRecoveryDeterministicOutcomeSpec :
    DeterministicOutcomeSpec LambdaParameterRecoveryParses
      LambdaParameterRecoveryRejects where
  successOutputUnique := LambdaParameterRecoveryParses.output_unique
  successRejectDisjoint :=
    FunctionParameterRecoveryRejects.disjointLambdaParses

end Solcore.Syntax.DeclarativeGrammar
