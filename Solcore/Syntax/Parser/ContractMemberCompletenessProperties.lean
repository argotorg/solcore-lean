import Solcore.Syntax.Parser.ContractDeclarationTotalityProperties
import Solcore.Syntax.Parser.CoreContractDeclarationExactnessProperties
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties

/-! Complete ordinary grammar correspondence for production contract fields
and attribute-free or derive-aware members. Only input validity is required. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Independent production-field success is exactly execution with the same
AST and declarative remainder on a valid input. -/
theorem contractFieldPublic_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : ContractField} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractFieldOrdinaryParses
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, contractField expression input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok (contractField expression)
    contractFieldPublic_exactOutcomeSpec
    (Solcore.Syntax.Parser.contractField_ne_invariant input inputValid)
    (contractField_success_ordinaryOutcome_sound expression
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      expression_success_ordinary_sound)
    (contractField_reject_ordinaryOutcome_sound expression
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      DeclarativeGrammar.CoreExpressionPublicRejects
      expression_success_ordinary_sound expression_reject_ordinary_sound)

/-- Independent production-field rejection is exactly execution at the same
declarative endpoint; failure diagnostics remain existential. -/
theorem contractFieldPublic_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractFieldRejects
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      DeclarativeGrammar.CoreExpressionPublicRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, contractField expression input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject (contractField expression)
    contractFieldPublic_exactOutcomeSpec
    (Solcore.Syntax.Parser.contractField_ne_invariant input inputValid)
    (contractField_success_ordinaryOutcome_sound expression
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      expression_success_ordinary_sound)
    (contractField_reject_ordinaryOutcome_sound expression
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      DeclarativeGrammar.CoreExpressionPublicRejects
      expression_success_ordinary_sound expression_reject_ordinary_sound)

/-- Attribute-free member grammar success is exactly execution with the same
member AST and declarative remainder. -/
theorem contractMemberCore_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, contractMemberCore input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok contractMemberCore
    contractMemberCore_exactOutcomeSpec
    (productionContractMemberCore_invariantFreeOnValid.ne_invariant
      input inputValid)
    contractMemberCore_success_ordinaryOutcome_sound
    contractMemberCore_reject_ordinaryOutcome_sound

/-- Attribute-free member grammar rejection is exactly execution at the same
declarative endpoint, without fixing failure diagnostics. -/
theorem contractMemberCore_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractMemberCoreRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, contractMemberCore input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject contractMemberCore
    contractMemberCore_exactOutcomeSpec
    (productionContractMemberCore_invariantFreeOnValid.ne_invariant
      input inputValid)
    contractMemberCore_success_ordinaryOutcome_sound
    contractMemberCore_reject_ordinaryOutcome_sound

/-- Derive-aware member grammar success is exactly execution with the same
member AST, including any attached attribute, and declarative remainder. -/
theorem contractMemberWithAttribute_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractMemberOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, contractMemberWithAttribute input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok contractMemberWithAttribute
    contractMemberWithAttribute_exactOutcomeSpec
    (productionContractMemberWithAttribute_ne_invariant input inputValid)
    contractMemberWithAttribute_success_ordinaryOutcome_sound
    contractMemberWithAttribute_reject_ordinaryOutcome_sound

/-- Derive-aware member grammar rejection is exactly execution at the same
declarative endpoint, without fixing failure diagnostics. -/
theorem contractMemberWithAttribute_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractMemberRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, contractMemberWithAttribute input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject contractMemberWithAttribute
    contractMemberWithAttribute_exactOutcomeSpec
    (productionContractMemberWithAttribute_ne_invariant input inputValid)
    contractMemberWithAttribute_success_ordinaryOutcome_sound
    contractMemberWithAttribute_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser.ContractInternals
