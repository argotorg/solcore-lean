import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties
import Solcore.Syntax.Parser.TypeFuelTotalityProperties

/-! Complete ordinary grammar correspondence for public Core types. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public type grammar success is exactly execution with the same type AST
and declarative remainder on a valid input. -/
theorem typeExpr_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : TypeExpr} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TypeExprOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, typeExpr input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok typeExpr typeExpr_exactOutcomeSpec
    (typeExpr_invariantFreeOnValid.ne_invariant input inputValid)
    typeExpr_success_sound typeExpr_reject_sound

/-- Public type grammar rejection is exactly execution at the same
declarative endpoint on a valid input. -/
theorem typeExpr_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TypeExprRejects input.declarativeRemainder rejected ↔
      ∃ failure output, typeExpr input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject typeExpr typeExpr_exactOutcomeSpec
    (typeExpr_invariantFreeOnValid.ne_invariant input inputValid)
    typeExpr_success_sound typeExpr_reject_sound

end Solcore.Syntax.Parser
