import Solcore.Syntax.Parser.ConstructorSelectionSoundnessProperties

/-! External consumers for constructor-selection grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserConstructorSelectionSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @IdentifierParses
example := @ConstructorNamesParses
example := @ConstructorSelectionParses
example := @identifier_success_sound
example := @requireConstructorNames_success_shape
example := @constructorSelection_success_sound
example := @constructorSelection_success_sound_and_validFor

example {input next : State} {selection : ConstructorSelection}
    (inputValid : input.ValidFor)
    (result : ExportInternals.constructorSelection input =
      .ok selection next) :
    ConstructorSelectionParses input.declarativeRemainder selection
        next.declarativeRemainder ∧
      selection.ValidFor input.file :=
  constructorSelection_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserConstructorSelectionSoundnessProperties
