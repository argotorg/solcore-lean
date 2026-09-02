import Solcore.Syntax.Parser.ReturnClauseOrdinaryRejectionSoundnessProperties

/-! External consumers for exact function return-clause outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserReturnClauseSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalReturnClauseParses
example := @OptionalReturnClauseRejects
example := @optionalReturnClauseDeterministicOutcomeSpec
example := @returnClause_success_sound
example := @returnClause_success_sound_and_validFor
example := @returnClause_reject_sound
example := @returnClause_ordinaryOutcome_sound

example {input next : State} {clause : Option ReturnClause}
    (result : returnClause input = .ok clause next) :
    OptionalReturnClauseParses input.declarativeRemainder clause
      next.declarativeRemainder :=
  returnClause_success_sound result

example {input next : State} {clause : Option ReturnClause}
    (inputValid : input.ValidFor)
    (result : returnClause input = .ok clause next) :
    OptionalReturnClauseParses input.declarativeRemainder clause
        next.declarativeRemainder ∧
      Option.ValidFor ReturnClause.ValidFor input.file clause :=
  returnClause_success_sound_and_validFor inputValid result

example {input rejected : State} {failure : Failure}
    (result : returnClause input = .reject failure rejected) :
    OptionalReturnClauseRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  returnClause_reject_sound result

end Solcore.Test.SyntaxParserReturnClauseSoundnessProperties
