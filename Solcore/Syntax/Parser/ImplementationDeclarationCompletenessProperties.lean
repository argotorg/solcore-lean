import Solcore.Syntax.Parser.CoreImplDeclarationExactnessProperties
import Solcore.Syntax.Parser.ImplDeclarationTotalityProperties
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties

/-! Complete ordinary grammar correspondence for implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Implementation grammar success is exactly execution with the same AST
and declarative remainder on a valid input. -/
theorem implDecl_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : ImplDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ImplDeclOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, implDecl input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok implDecl implDecl_exactOutcomeSpec
    (implDecl_invariantFreeOnValid.ne_invariant input inputValid)
    implDecl_success_ordinaryOutcome_sound implDecl_reject_ordinaryOutcome_sound

/-- Implementation grammar rejection is exactly execution at the same
declarative endpoint on a valid input. -/
theorem implDecl_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ImplDeclRejects input.declarativeRemainder rejected ↔
      ∃ failure output, implDecl input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject implDecl implDecl_exactOutcomeSpec
    (implDecl_invariantFreeOnValid.ne_invariant input inputValid)
    implDecl_success_ordinaryOutcome_sound implDecl_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser
