import Solcore.Syntax.DeclarativeTopItemOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.DeriveAttributeOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PlainTopItemOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TopItemDeriveAttachmentOrdinarySoundnessProperties

/-! Broad ordinary-rejection reflection for derive-aware top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem topItemHashPresentAt_of_isSymbol_eq_true {input : State}
    (present : isSymbol input .hash = true) :
    DeclarativeGrammar.PlainTopItemTokenPresentAt
      input.declarativeRemainder (.symbol .hash) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .hash .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses .hash .topItem result).1⟩

/-- Every executable top-item rejection records the exact first rejecting
stage. Pure derive attachment cannot reject. -/
theorem topItem_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : topItem input = .reject failure rejected) :
    DeclarativeGrammar.TopItemRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold topItem at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact .plainRejected
        (symbolAbsentAt_of_isSymbol_eq_false .hash hashPresent)
        (plainTopItem_ordinaryOutcome_sound.2 result)
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | invariant error => simp [deriveResult] at result
      | reject deriveFailure deriveRejected =>
          simp only [deriveResult] at result
          cases result
          exact .deriveRejected
            (topItemHashPresentAt_of_isSymbol_eq_true hashPresent)
            (deriveAttribute_ordinaryOutcome_sound.2 deriveResult)
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases plainResult : plainTopItem afterDerive with
          | invariant error => simp [plainResult] at result
          | reject plainFailure plainRejected =>
              simp only [plainResult] at result
              cases result
              exact .derivedPlainRejected
                (topItemHashPresentAt_of_isSymbol_eq_true hashPresent)
                (deriveAttribute_ordinaryOutcome_sound.1 deriveResult)
                (plainTopItem_ordinaryOutcome_sound.2 plainResult)
          | ok plainItem afterPlain =>
              simp only [plainResult] at result
              rcases attachDeriveAttribute_total_success derive plainItem
                  afterPlain with
                ⟨attached, output, attachedResult⟩
              rw [attachedResult] at result
              contradiction

end Solcore.Syntax.Parser.FileInternals
