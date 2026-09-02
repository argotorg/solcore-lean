import Solcore.Syntax.DeclarativeDeriveAttributeOutcomeProperties
import Solcore.Syntax.DeclarativePlainTopItemOutcomeProperties
import Solcore.Syntax.DeclarativeTopItemDeriveAttachmentProperties
import Solcore.Syntax.DeclarativeTopItemOutcomeGrammar

/-! Deterministic broad ordinary outcomes for public top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {input : Remainder} {kind : TokenKind}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : PlainTopItemTokenPresentAt input kind) : False := by
  unfold PlainTopItemTokenPresentAt at present
  exact absent present

/-- Public top-item success has one final remainder. -/
theorem TopItemOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : TopItemOrdinaryParses input left afterLeft)
    (rightParsed : TopItemOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | plain leftHashAbsent leftPlainParsed =>
      cases rightParsed with
      | plain rightHashAbsent rightPlainParsed =>
          exact plainTopItemDeterministicOutcomeSpec.successOutputUnique
            leftPlainParsed rightPlainParsed
      | derived rightHashPresent rightDeriveParsed rightPlainParsed
          rightAttached =>
          exact False.elim
            (absent_conflicts_token leftHashAbsent rightHashPresent)
  | derived leftHashPresent leftDeriveParsed leftPlainParsed leftAttached =>
      cases rightParsed with
      | plain rightHashAbsent rightPlainParsed =>
          exact False.elim
            (absent_conflicts_token rightHashAbsent leftHashPresent)
      | derived rightHashPresent rightDeriveParsed rightPlainParsed
          rightAttached =>
          have afterDeriveEq :=
            deriveAttributeDeterministicOutcomeSpec.successOutputUnique
              leftDeriveParsed rightDeriveParsed
          cases afterDeriveEq
          exact plainTopItemDeterministicOutcomeSpec.successOutputUnique
            leftPlainParsed rightPlainParsed

/-- Every exact public top-item rejection excludes plain and derive-prefixed
success. -/
theorem TopItemRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : TopItemRejects input rejected) :
    ¬ ∃ item output, TopItemOrdinaryParses input item output := by
  rintro ⟨item, output, successful⟩
  cases rejection with
  | plainRejected rejectedHashAbsent plainRejected =>
      cases successful with
      | plain successfulHashAbsent plainParsed =>
          exact plainTopItemDeterministicOutcomeSpec.successRejectDisjoint
            plainRejected ⟨_, _, plainParsed⟩
      | derived successfulHashPresent deriveParsed plainParsed attached =>
          exact absent_conflicts_token rejectedHashAbsent
            successfulHashPresent
  | deriveRejected rejectedHashPresent deriveRejected =>
      cases successful with
      | plain successfulHashAbsent plainParsed =>
          exact absent_conflicts_token successfulHashAbsent
            rejectedHashPresent
      | derived successfulHashPresent deriveParsed plainParsed attached =>
          exact deriveAttributeDeterministicOutcomeSpec.successRejectDisjoint
            deriveRejected ⟨_, _, deriveParsed⟩
  | derivedPlainRejected rejectedHashPresent rejectedDeriveParsed
      plainRejected =>
      cases successful with
      | plain successfulHashAbsent plainParsed =>
          exact absent_conflicts_token successfulHashAbsent
            rejectedHashPresent
      | derived successfulHashPresent successfulDeriveParsed plainParsed
          attached =>
          have afterDeriveEq :=
            deriveAttributeDeterministicOutcomeSpec.successOutputUnique
              rejectedDeriveParsed successfulDeriveParsed
          cases afterDeriveEq
          exact plainTopItemDeterministicOutcomeSpec.successRejectDisjoint
            plainRejected ⟨_, _, plainParsed⟩

/-- Public top-item outcomes have deterministic successful remainders and
exact rejection/success exclusion. -/
theorem topItemDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TopItemOrdinaryParses TopItemRejects where
  successOutputUnique := TopItemOrdinaryParses.output_unique
  successRejectDisjoint := TopItemRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
