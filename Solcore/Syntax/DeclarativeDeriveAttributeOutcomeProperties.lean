import Solcore.Syntax.DeclarativeDeriveAttributeOutcomeGrammar
import Solcore.Syntax.DeclarativeDeriveAttributeRecoveryOutcomeProperties
import Solcore.Syntax.DeclarativeDeriveAttributeValidOutcomeProperties

/-! Deterministic broad ordinary outcomes for public derive attributes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Prioritized normal-or-recovered derive success has one final remainder. -/
theorem DeriveAttributeOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeOrdinaryParses input left afterLeft)
    (rightParsed : DeriveAttributeOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | normal leftNormal =>
      cases rightParsed with
      | normal rightNormal =>
          exact deriveAttributeValidDeterministicOutcomeSpec.successOutputUnique
            leftNormal rightNormal
      | recovered rightValidRejection rightRecovered =>
          exact False.elim
            (deriveAttributeValidDeterministicOutcomeSpec.successRejectDisjoint
              rightValidRejection ⟨_, _, leftNormal⟩)
  | recovered leftValidRejection leftRecovered =>
      cases rightParsed with
      | normal rightNormal =>
          exact False.elim
            (deriveAttributeValidDeterministicOutcomeSpec.successRejectDisjoint
              leftValidRejection ⟨_, _, rightNormal⟩)
      | recovered rightValidRejection rightRecovered =>
          exact
            deriveAttributeRecoveredDeterministicOutcomeSpec.successOutputUnique
              leftRecovered rightRecovered

/-- Exact rejection of both branches excludes normal and recovered public
success alike. -/
theorem DeriveAttributeRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : DeriveAttributeRejects input rejected) :
    ¬ ∃ value output, DeriveAttributeOrdinaryParses input value output := by
  rintro ⟨value, output, successful⟩
  cases rejection with
  | both validRejection recoveredRejection =>
      cases successful with
      | normal normalParsed =>
          exact
            deriveAttributeValidDeterministicOutcomeSpec.successRejectDisjoint
              validRejection ⟨_, _, normalParsed⟩
      | recovered otherValidRejection recoveredParsed =>
          exact
            deriveAttributeRecoveredDeterministicOutcomeSpec.successRejectDisjoint
              recoveredRejection ⟨_, _, recoveredParsed⟩

/-- Public derive attributes have deterministic and exclusive ordinary
outcomes without claiming value or rejection-endpoint uniqueness. -/
theorem deriveAttributeDeterministicOutcomeSpec :
    DeterministicOutcomeSpec DeriveAttributeOrdinaryParses
      DeriveAttributeRejects where
  successOutputUnique := DeriveAttributeOrdinaryParses.output_unique
  successRejectDisjoint := DeriveAttributeRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
