import Solcore.Syntax.Parser.ContractDeclarationTotalityProperties
import Solcore.Syntax.Parser.CoreContractDeclarationExactnessProperties
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties

/-! Complete ordinary grammar correspondence for contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Contract grammar success is exactly execution with the same AST and
declarative remainder on a valid input. -/
theorem contractDecl_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : ContractDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractDeclOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, contractDecl input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok contractDecl contractDecl_exactOutcomeSpec
    (contractDecl_invariantFreeOnValid.ne_invariant input inputValid)
    contractDecl_success_ordinaryOutcome_sound contractDecl_reject_ordinaryOutcome_sound

/-- Contract grammar rejection is exactly execution at the same
declarative endpoint on a valid input. -/
theorem contractDecl_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractDeclRejects input.declarativeRemainder rejected ↔
      ∃ failure output, contractDecl input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject contractDecl contractDecl_exactOutcomeSpec
    (contractDecl_invariantFreeOnValid.ne_invariant input inputValid)
    contractDecl_success_ordinaryOutcome_sound contractDecl_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser
