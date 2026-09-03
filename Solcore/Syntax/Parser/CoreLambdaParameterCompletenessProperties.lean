import Solcore.Syntax.Parser.CoreLambdaParameterOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.LambdaParameterCoreTotalityProperties
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties

/-! Complete public lambda-parameter correspondence, including ordinary
recovery and the existing rewound rejection endpoint. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public lambda-parameter grammar success is exactly execution with the
same parameter AST and declarative remainder on a valid input. -/
theorem lambdaParameter_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : LambdaParameter} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.LambdaParameterOrdinaryParses
      DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects
        input.declarativeRemainder value remainder ↔
      ∃ output, lambdaParameter input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok lambdaParameter lambdaParameter_exactOutcomeSpec
    (lambdaParameter_invariantFreeOnValid.ne_invariant input inputValid)
    (lambdaParameter_success_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects
      typeExpr_success_sound typeExpr_reject_sound)
    (lambdaParameter_reject_ordinaryOutcome_sound DeclarativeGrammar.TypeExprRejects
      typeExpr_reject_sound)

/-- Public lambda-parameter grammar rejection is exactly execution at its
declarative endpoint, without identifying emitted diagnostics. -/
theorem lambdaParameter_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.LambdaParameterRejects DeclarativeGrammar.TypeExprRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, lambdaParameter input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject lambdaParameter lambdaParameter_exactOutcomeSpec
    (lambdaParameter_invariantFreeOnValid.ne_invariant input inputValid)
    (lambdaParameter_success_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects
      typeExpr_success_sound typeExpr_reject_sound)
    (lambdaParameter_reject_ordinaryOutcome_sound DeclarativeGrammar.TypeExprRejects
      typeExpr_reject_sound)

end Solcore.Syntax.Parser
