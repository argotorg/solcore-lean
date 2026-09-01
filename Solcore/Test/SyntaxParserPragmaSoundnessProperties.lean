import Solcore.Syntax.Parser.PragmaSoundnessProperties

/-! External consumers for canonical pragma success soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TokenAt
example := @PragmaItemsTailParses
example := @PragmaItemsParses
example := @PragmaDeclParses
example := @State.declarativeRemainder
example := @pragmaDecl_success_sound
example := @pragmaDecl_success_sound_and_validFor

example {input next : State} {declaration : PragmaDecl}
    (result : pragmaDecl input = .ok declaration next) :
    PragmaDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  pragmaDecl_success_sound result

example {input next : State} {declaration : PragmaDecl}
    (inputValid : input.ValidFor)
    (result : pragmaDecl input = .ok declaration next) :
    PragmaDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  pragmaDecl_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserPragmaSoundnessProperties
