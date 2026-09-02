import Solcore.Syntax.DeclarativeDeriveAttributeOutcomeProperties
import Solcore.Syntax.DeclarativeDeriveAttributeRecoveryExactnessProperties
import Solcore.Syntax.DeclarativeDeriveAttributeValidExactnessProperties

/-! Full functionality of public prioritized derive-attribute outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Prioritized normal-or-recovered success has one exact AST value. -/
theorem DeriveAttributeOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeOrdinaryParses input left afterLeft)
    (rightParsed : DeriveAttributeOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | normal leftNormal =>
      cases rightParsed with
      | normal rightNormal =>
          exact deriveAttributeValidExactOutcomeSpec.successValueUnique
            leftNormal rightNormal
      | recovered rightValidRejects rightRecovered =>
          exact False.elim
            (deriveAttributeValidExactOutcomeSpec.successRejectDisjoint
              rightValidRejects ⟨_, _, leftNormal⟩)
  | recovered leftValidRejects leftRecovered =>
      cases rightParsed with
      | normal rightNormal =>
          exact False.elim
            (deriveAttributeValidExactOutcomeSpec.successRejectDisjoint
              leftValidRejects ⟨_, _, rightNormal⟩)
      | recovered rightValidRejects rightRecovered =>
          exact deriveAttributeRecoveredExactOutcomeSpec.successValueUnique
            leftRecovered rightRecovered

/-- Prioritized normal-or-recovered success fixes its AST and final
remainder. -/
theorem DeriveAttributeOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeOrdinaryParses input left afterLeft)
    (rightParsed : DeriveAttributeOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Public rejection has one exact endpoint, namely recovery's first failing
endpoint after both branches reject. -/
theorem DeriveAttributeRejects.output_unique
    {input left right : Remainder}
    (leftRejects : DeriveAttributeRejects input left)
    (rightRejects : DeriveAttributeRejects input right) : left = right := by
  cases leftRejects with
  | both leftValidRejects leftRecoveredRejects =>
      cases rightRejects with
      | both rightValidRejects rightRecoveredRejects =>
          exact
            deriveAttributeRecoveredExactOutcomeSpec.rejectOutputUnique
              leftRecoveredRejects rightRecoveredRejects

/-- Public derive attributes have fully functional prioritized success and
rejection outcomes. -/
theorem deriveAttributeExactOutcomeSpec :
    ExactDeterministicOutcomeSpec DeriveAttributeOrdinaryParses
      DeriveAttributeRejects where
  toDeterministicOutcomeSpec := deriveAttributeDeterministicOutcomeSpec
  successValueUnique := DeriveAttributeOrdinaryParses.value_unique
  rejectOutputUnique := DeriveAttributeRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
