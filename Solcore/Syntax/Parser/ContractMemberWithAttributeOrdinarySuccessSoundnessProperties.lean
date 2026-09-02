import Solcore.Syntax.DeclarativeContractMemberWithAttributeOutcomeGrammar
import Solcore.Syntax.Parser.ContractDeriveAttachmentOrdinarySoundnessProperties
import Solcore.Syntax.Parser.ContractMemberCoreOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.DeriveAttributeOrdinaryOutcomeSoundnessProperties

/-! Broad ordinary-success reflection for derive-aware contract members. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

private theorem hashPresentAt_of_isSymbol_eq_true {input : State}
    (present : isSymbol input .hash = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder (.symbol .hash) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .hash .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses .hash .topItem result).1⟩

/-- Every successful public contract-member parse follows the exact plain or
derive-aware broad ordinary branch, without a diagnostic-free premise. -/
theorem contractMemberWithAttribute_success_ordinaryOutcome_sound
    {input output : State} {member : ContractMember}
    (result : contractMemberWithAttribute input = .ok member output) :
    DeclarativeGrammar.ContractMemberOrdinaryParses
      input.declarativeRemainder member output.declarativeRemainder := by
  unfold contractMemberWithAttribute at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact .plain
        (symbolAbsentAt_of_isSymbol_eq_false .hash hashPresent)
        (contractMemberCore_success_ordinaryOutcome_sound result)
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | invariant error => simp [deriveResult] at result
      | reject failure rejected => simp [deriveResult] at result
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases coreResult : contractMemberCore afterDerive with
          | invariant error => simp [coreResult] at result
          | reject failure rejected => simp [coreResult] at result
          | ok coreMember afterCore =>
              simp only [coreResult] at result
              have attachment :=
                attachContractDerive_success_ordinaryOutcome_sound result
              rw [attachment.2]
              exact .derived
                (hashPresentAt_of_isSymbol_eq_true hashPresent)
                (deriveAttribute_success_ordinaryOutcome_sound deriveResult)
                (contractMemberCore_success_ordinaryOutcome_sound coreResult)
                attachment.1

end Solcore.Syntax.Parser.ContractInternals
