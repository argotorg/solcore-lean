import Solcore.Syntax.DeclarativeTopItemOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.DeriveAttributeOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PlainTopItemOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TopItemDeriveAttachmentOrdinarySoundnessProperties

/-! Broad ordinary-success reflection for derive-aware top-item dispatch. -/

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

/-- Every executable top-item success follows the exact plain or derive-aware
broad ordinary branch, without a diagnostic-free premise. -/
theorem topItem_success_ordinaryOutcome_sound
    {input output : State} {item : TopItem}
    (result : topItem input = .ok item output) :
    DeclarativeGrammar.TopItemOrdinaryParses
      input.declarativeRemainder item output.declarativeRemainder := by
  unfold topItem at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact .plain
        (symbolAbsentAt_of_isSymbol_eq_false .hash hashPresent)
        (plainTopItem_ordinaryOutcome_sound.1 result)
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | invariant error => simp [deriveResult] at result
      | reject failure rejected => simp [deriveResult] at result
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases plainResult : plainTopItem afterDerive with
          | invariant error => simp [plainResult] at result
          | reject failure rejected => simp [plainResult] at result
          | ok plainItem afterPlain =>
              simp only [plainResult] at result
              have attachment :=
                attachDeriveAttribute_success_ordinaryOutcome_sound result
              rw [attachment.2]
              exact .derived
                (topItemHashPresentAt_of_isSymbol_eq_true hashPresent)
                (deriveAttribute_ordinaryOutcome_sound.1 deriveResult)
                (plainTopItem_ordinaryOutcome_sound.1 plainResult)
                attachment.1

end Solcore.Syntax.Parser.FileInternals
