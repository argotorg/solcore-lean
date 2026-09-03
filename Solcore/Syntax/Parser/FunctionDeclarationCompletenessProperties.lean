import Solcore.Syntax.Parser.ContractEntryDeclarationTotalityProperties
import Solcore.Syntax.Parser.CoreFunctionDeclarationExactnessProperties
import Solcore.Syntax.Parser.FunctionDeclarationTotalityProperties
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties

/-! Complete ordinary grammar correspondence for named functions and
contract entry declarations on valid parser states. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- At either function location, grammar success is exactly execution with
the same function AST and declarative remainder on a valid input. -/
theorem functionDecl_ordinary_success_iff (location : FunctionLocation)
    {input : State} (inputValid : input.ValidFor)
    {value : FunctionDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.FunctionDeclOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, functionDecl location input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok (functionDecl location) functionDecl_exactOutcomeSpec
    ((functionDecl_invariantFreeOnValid location).ne_invariant input inputValid)
    (functionDecl_success_ordinaryOutcome_sound location)
    (functionDecl_reject_ordinaryOutcome_sound location)

/-- At either function location, grammar rejection is exactly execution at
the same declarative endpoint on a valid input. -/
theorem functionDecl_ordinary_reject_iff (location : FunctionLocation)
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.FunctionDeclRejects input.declarativeRemainder rejected ↔
      ∃ failure output, functionDecl location input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject (functionDecl location) functionDecl_exactOutcomeSpec
    ((functionDecl_invariantFreeOnValid location).ne_invariant input inputValid)
    (functionDecl_success_ordinaryOutcome_sound location)
    (functionDecl_reject_ordinaryOutcome_sound location)

/-- Constructor grammar success is exactly execution with the same AST and
declarative remainder on a valid input. -/
theorem constructorDecl_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : ConstructorDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ConstructorDeclOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, constructorDecl input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok constructorDecl constructorDecl_exactOutcomeSpec
    (constructorDecl_invariantFreeOnValid.ne_invariant input inputValid)
    constructorDecl_success_ordinaryOutcome_sound constructorDecl_reject_ordinaryOutcome_sound

/-- Constructor grammar rejection is exactly execution at the same
declarative endpoint on a valid input. -/
theorem constructorDecl_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ConstructorDeclRejects input.declarativeRemainder rejected ↔
      ∃ failure output, constructorDecl input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject constructorDecl constructorDecl_exactOutcomeSpec
    (constructorDecl_invariantFreeOnValid.ne_invariant input inputValid)
    constructorDecl_success_ordinaryOutcome_sound constructorDecl_reject_ordinaryOutcome_sound

/-- Fallback grammar success is exactly execution with the same AST and
declarative remainder on a valid input. -/
theorem fallbackDecl_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : FallbackDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.FallbackDeclOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, fallbackDecl input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok fallbackDecl fallbackDecl_exactOutcomeSpec
    (fallbackDecl_invariantFreeOnValid.ne_invariant input inputValid)
    fallbackDecl_success_ordinaryOutcome_sound fallbackDecl_reject_ordinaryOutcome_sound

/-- Fallback grammar rejection is exactly execution at the same
declarative endpoint on a valid input. -/
theorem fallbackDecl_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.FallbackDeclRejects input.declarativeRemainder rejected ↔
      ∃ failure output, fallbackDecl input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject fallbackDecl fallbackDecl_exactOutcomeSpec
    (fallbackDecl_invariantFreeOnValid.ne_invariant input inputValid)
    fallbackDecl_success_ordinaryOutcome_sound fallbackDecl_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser
