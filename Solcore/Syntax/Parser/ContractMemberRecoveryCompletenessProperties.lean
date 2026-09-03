import Solcore.Syntax.Parser.ContractMemberRecoveryOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties

/-! Complete standalone contract-member recovery correspondence for arbitrary
input states; recovery's production fuel needs no validity premise. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Independent recovery success is exactly execution with the same recovered
member AST and declarative remainder, even without input validity. -/
theorem recoverContractMember_ordinary_success_iff
    {input : State} {value : ContractMember}
    {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractMemberRecoveryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, recoverContractMember input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok recoverContractMember
    recoverContractMember_exactOutcomeSpec
    (recoverContractMember_ne_invariant input)
    recoverContractMember_success_ordinaryOutcome_sound
    recoverContractMember_reject_ordinaryOutcome_sound

/-- Independent recovery rejection is exactly execution at the same
declarative endpoint, leaving diagnostics existential. -/
theorem recoverContractMember_ordinary_reject_iff
    {input : State} {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractMemberRecoveryRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, recoverContractMember input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject recoverContractMember
    recoverContractMember_exactOutcomeSpec
    (recoverContractMember_ne_invariant input)
    recoverContractMember_success_ordinaryOutcome_sound
    recoverContractMember_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser.ContractInternals
