import Solcore.Syntax.DeclarativeContractMemberWithAttributeOutcomeGrammar
import Solcore.Syntax.Parser.ContractDeriveAttachmentOrdinarySoundnessProperties
import Solcore.Syntax.Parser.ContractMemberCoreOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.DeriveAttributeOrdinaryOutcomeSoundnessProperties

/-! Broad ordinary-rejection reflection for derive-aware contract members. -/

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

/-- Every executable public contract-member rejection records the exact first
rejecting stage.  Pure derive attachment cannot reject. -/
theorem contractMemberWithAttribute_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : contractMemberWithAttribute input = .reject failure rejected) :
    DeclarativeGrammar.ContractMemberRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold contractMemberWithAttribute at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact .plainCoreRejected
        (symbolAbsentAt_of_isSymbol_eq_false .hash hashPresent)
        (contractMemberCore_reject_ordinaryOutcome_sound result)
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | invariant error => simp [deriveResult] at result
      | reject deriveFailure deriveRejected =>
          simp only [deriveResult] at result
          cases result
          exact .deriveRejected
            (hashPresentAt_of_isSymbol_eq_true hashPresent)
            (deriveAttribute_reject_ordinaryOutcome_sound deriveResult)
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases coreResult : contractMemberCore afterDerive with
          | invariant error => simp [coreResult] at result
          | reject coreFailure coreRejected =>
              simp only [coreResult] at result
              cases result
              exact .derivedCoreRejected
                (hashPresentAt_of_isSymbol_eq_true hashPresent)
                (deriveAttribute_success_ordinaryOutcome_sound deriveResult)
                (contractMemberCore_reject_ordinaryOutcome_sound coreResult)
          | ok coreMember afterCore =>
              simp only [coreResult] at result
              rcases attachContractDerive_total_success derive coreMember
                  afterCore with
                ⟨attached, output, attachedResult⟩
              rw [attachedResult] at result
              contradiction

end Solcore.Syntax.Parser.ContractInternals
