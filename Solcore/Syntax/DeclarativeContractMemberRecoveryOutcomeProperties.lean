import Solcore.Syntax.DeclarativeContractMemberRecoveryOutcomeGrammar

/-! Functionality and outcome exclusion for contract-member recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- A contract-member recovery scan has one final remainder. -/
theorem ContractMemberRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.ContractMember} {afterLeft afterRight : Remainder},
      ContractMemberRecoveryScanParses first leftLast input left afterLeft →
      ContractMemberRecoveryScanParses first rightLast input right afterRight →
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

/-- Complete ordinary contract-member recovery has one final remainder. -/
theorem ContractMemberRecoveryParses.output_unique
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberRecoveryParses input left afterLeft)
    (rightParsed : ContractMemberRecoveryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Every contract-member recovery rejection is non-consuming. -/
theorem ContractMemberRecoveryRejects.output_eq
    {input rejected : Remainder}
    (rejection : ContractMemberRecoveryRejects input rejected) :
    rejected = input := by
  cases rejection <;> rfl

/-- An unavailable mandatory first token excludes every recovery success. -/
theorem ContractMemberRecoveryRejects.disjointParses
    {input rejected : Remainder}
    (rejection : ContractMemberRecoveryRejects input rejected) :
    ¬ ∃ member output, ContractMemberRecoveryParses input member output := by
  rintro ⟨member, output, parsed⟩
  cases parsed with
  | recovered current scan =>
      cases rejection with
      | windowEnd atEnd =>
          exact Nat.not_lt_of_ge atEnd current.1
      | missingToken inside missing =>
          rw [current.2] at missing
          contradiction

/-- Deterministic ordinary outcome contract for contract-member recovery. -/
theorem contractMemberRecoveryDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ContractMemberRecoveryParses
      ContractMemberRecoveryRejects where
  successOutputUnique := ContractMemberRecoveryParses.output_unique
  successRejectDisjoint := ContractMemberRecoveryRejects.disjointParses

end Solcore.Syntax.DeclarativeGrammar
