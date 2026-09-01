import Solcore.Syntax.Parser.ReturnClauseSoundnessProperties

/-! External consumers for function return-clause grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserReturnClauseSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalReturnClauseParses
example := @returnClause_success_sound
example := @returnClause_success_sound_and_validFor

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

end Solcore.Test.SyntaxParserReturnClauseSoundnessProperties
