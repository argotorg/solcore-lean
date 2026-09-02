import Solcore.Syntax.Parser.HidingClauseOrdinaryOutcomeSoundnessProperties

/-! External consumers for hiding-clause grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserHidingClauseSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @NonemptySelectorListParses
example := @HidingClauseParses
example := @OptionalHidingParses
example := @HidingClauseOrdinaryParses
example := @HidingClauseRejects
example := @OptionalHidingOrdinaryParses
example := @OptionalHidingRejects
example := @hidingClauseDeterministicOutcomeSpec
example := @optionalHidingDeterministicOutcomeSpec
example := @contextualAbsentAt_of_isContextual_eq_false
example := @requireSelectorNames_success_shape
example := @hidingClause_success_sound
example := @hidingClause_success_sound_and_validFor
example := @optionalHiding_success_sound
example := @optionalHiding_success_sound_and_validFor
example := @hidingClause_ordinaryOutcome_sound
example := @hidingClause_ordinaryOutcomeSpec
example := @optionalHiding_ordinaryOutcome_sound
example := @optionalHiding_ordinaryOutcomeSpec

example {input next : State} {hidden : Option HidingClause}
    (inputValid : input.ValidFor)
    (result : ImportInternals.optionalHiding input = .ok hidden next) :
    OptionalHidingParses input.declarativeRemainder hidden
        next.declarativeRemainder ∧
      Option.ValidFor HidingClause.ValidFor input.file hidden :=
  optionalHiding_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserHidingClauseSoundnessProperties
