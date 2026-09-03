import Solcore.Syntax.Parser.CanonicalParserTotalityProperties
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties
import Solcore.Syntax.Parser.TopItemExactnessProperties

/-! Complete plain and derive-aware top-item grammar correspondence on valid
states, retaining complete ASTs and declarative success or rejection endpoints. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Independent plainTopItem success is exactly executable success with the same
AST and declarative remainder on a valid input. -/
theorem plainTopItem_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : TopItem} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.PlainTopItemOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, plainTopItem input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok plainTopItem plainTopItem_exactOutcomeSpec
    (productionPlainTopItem_ne_invariant input inputValid)
    plainTopItem_success_ordinaryOutcome_sound plainTopItem_reject_ordinaryOutcome_sound

/-- Independent plainTopItem rejection is exactly executable rejection at the
same declarative endpoint; failure diagnostics remain existential. -/
theorem plainTopItem_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.PlainTopItemRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, plainTopItem input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject plainTopItem plainTopItem_exactOutcomeSpec
    (productionPlainTopItem_ne_invariant input inputValid)
    plainTopItem_success_ordinaryOutcome_sound plainTopItem_reject_ordinaryOutcome_sound

/-- Independent topItem success is exactly executable success with the same
AST and declarative remainder on a valid input. -/
theorem topItem_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : TopItem} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TopItemOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, topItem input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok topItem topItem_exactOutcomeSpec
    (productionTopItem_ne_invariant input inputValid)
    topItem_success_ordinaryOutcome_sound topItem_reject_ordinaryOutcome_sound

/-- Independent topItem rejection is exactly executable rejection at the
same declarative endpoint; failure diagnostics remain existential. -/
theorem topItem_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TopItemRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, topItem input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject topItem topItem_exactOutcomeSpec
    (productionTopItem_ne_invariant input inputValid)
    topItem_success_ordinaryOutcome_sound topItem_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser.FileInternals
