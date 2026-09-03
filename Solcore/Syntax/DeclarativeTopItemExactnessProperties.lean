import Solcore.Syntax.DeclarativeDeriveAttributeExactnessProperties
import Solcore.Syntax.DeclarativeTopItemOutcomeProperties

/-! Exact top-item outcomes transported through leading derive attachment. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact plain items and derive attributes fix the complete attached item AST. -/
theorem TopItemOrdinaryParses.value_unique_of_plain
    (plainOutcomes : ExactDeterministicOutcomeSpec PlainTopItemOrdinaryParses PlainTopItemRejects)
    {input : Remainder} {left right : Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : TopItemOrdinaryParses input left afterLeft)
    (rightParsed : TopItemOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | plain absent leftPlain =>
      cases rightParsed with
      | plain _ rightPlain => exact plainOutcomes.successValueUnique leftPlain rightPlain
      | derived present _ _ _ => exact False.elim (absent present)
  | derived present leftDerive leftPlain leftAttached =>
      cases rightParsed with
      | plain absent _ => exact False.elim (absent present)
      | derived _ rightDerive rightPlain rightAttached =>
          rcases deriveAttributeExactOutcomeSpec.successResultUnique leftDerive rightDerive with
            ⟨deriveEq, inputEq⟩
          subst deriveEq
          subst inputEq
          have valueEq := plainOutcomes.successValueUnique leftPlain rightPlain
          subst valueEq
          exact leftAttached.output_unique rightAttached

/-- The committed derive/plain branch determines the first rejecting endpoint. -/
theorem TopItemRejects.output_unique_of_plain
    (plainOutcomes : ExactDeterministicOutcomeSpec PlainTopItemOrdinaryParses PlainTopItemRejects)
    {input left right : Remainder}
    (leftRejected : TopItemRejects input left)
    (rightRejected : TopItemRejects input right) : left = right := by
  cases leftRejected with
  | plainRejected absent leftPlain =>
      cases rightRejected with
      | plainRejected _ rightPlain => exact plainOutcomes.rejectOutputUnique leftPlain rightPlain
      | deriveRejected present _ => exact False.elim (absent present)
      | derivedPlainRejected present _ _ => exact False.elim (absent present)
  | deriveRejected present leftDerive =>
      cases rightRejected with
      | plainRejected absent _ => exact False.elim (absent present)
      | deriveRejected _ rightDerive =>
          exact deriveAttributeExactOutcomeSpec.rejectOutputUnique leftDerive rightDerive
      | derivedPlainRejected _ rightDerive _ =>
          exact False.elim (deriveAttributeExactOutcomeSpec.successRejectDisjoint
            leftDerive ⟨_, _, rightDerive⟩)
  | derivedPlainRejected present leftDerive leftPlain =>
      cases rightRejected with
      | plainRejected absent _ => exact False.elim (absent present)
      | deriveRejected _ rightDerive =>
          exact False.elim (deriveAttributeExactOutcomeSpec.successRejectDisjoint
            rightDerive ⟨_, _, leftDerive⟩)
      | derivedPlainRejected _ rightDerive rightPlain =>
          have inputEq := deriveAttributeExactOutcomeSpec.successOutputUnique
            leftDerive rightDerive
          subst inputEq
          exact plainOutcomes.rejectOutputUnique leftPlain rightPlain

/-- Exact plain top-items lift through derive priority and pure attachment. -/
theorem topItemExactOutcomeSpecOfPlain
    (plainOutcomes : ExactDeterministicOutcomeSpec PlainTopItemOrdinaryParses PlainTopItemRejects) :
    ExactDeterministicOutcomeSpec TopItemOrdinaryParses TopItemRejects where
  toDeterministicOutcomeSpec := topItemDeterministicOutcomeSpec
  successValueUnique := TopItemOrdinaryParses.value_unique_of_plain plainOutcomes
  rejectOutputUnique := TopItemRejects.output_unique_of_plain plainOutcomes

end Solcore.Syntax.DeclarativeGrammar
