import Solcore.Syntax.DeclarativeContractMemberRecoveryOutcomeProperties
import Solcore.Syntax.DeclarativeExactOutcomeSpec
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Full functionality of contract-member recovery outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A recovery scan with fixed first and last retained spans has one exact
error-member AST. -/
theorem ContractMemberRecoveryScanParses.value_unique :
    ∀ {first last : SourceSpan} {input : Remainder}
      {left right : Syntax.ContractMember}
      {afterLeft afterRight : Remainder},
      ContractMemberRecoveryScanParses first last input left afterLeft →
      ContractMemberRecoveryScanParses first last input right afterRight →
      left = right := by
  intro first last input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops =>
          exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- A recovery scan with fixed retained spans determines its AST and final
remainder. -/
theorem ContractMemberRecoveryScanParses.result_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberRecoveryScanParses first last input left
      afterLeft)
    (rightParsed : ContractMemberRecoveryScanParses first last input right
      afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Complete contract-member recovery has one exact error-member AST. -/
theorem ContractMemberRecoveryParses.value_unique
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberRecoveryParses input left afterLeft)
    (rightParsed : ContractMemberRecoveryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact leftScan.value_unique rightScan

/-- Complete contract-member recovery fixes its AST and final remainder. -/
theorem ContractMemberRecoveryParses.result_unique
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberRecoveryParses input left afterLeft)
    (rightParsed : ContractMemberRecoveryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- An unavailable mandatory token fixes the exact nonconsuming endpoint. -/
theorem ContractMemberRecoveryRejects.output_unique
    {input left right : Remainder}
    (leftRejects : ContractMemberRecoveryRejects input left)
    (rightRejects : ContractMemberRecoveryRejects input right) :
    left = right :=
  leftRejects.output_eq.trans rightRejects.output_eq.symm

/-- Contract-member recovery has fully functional success and rejection
outcomes. -/
theorem contractMemberRecoveryExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ContractMemberRecoveryParses
      ContractMemberRecoveryRejects where
  toDeterministicOutcomeSpec := contractMemberRecoveryDeterministicOutcomeSpec
  successValueUnique := ContractMemberRecoveryParses.value_unique
  rejectOutputUnique := ContractMemberRecoveryRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
