import Solcore.Syntax.Parser.GenericParametersSoundnessProperties

/-! External consumers for generic-parameter grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserGenericParametersSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @GenericParametersParses
example := @OptionalGenericParametersParses
example := @requireGenericParameters_success_shape
example := @genericParameters_success_sound
example := @genericParameters_success_sound_and_validFor
example := @optionalGenericParameters_success_sound
example := @optionalGenericParameters_success_sound_and_validFor

example {input next : State} {parameters : GenericParameters}
    (result : genericParameters input = .ok parameters next) :
    GenericParametersParses input.declarativeRemainder parameters
      next.declarativeRemainder :=
  genericParameters_success_sound result

example {input next : State} {parameters : Option GenericParameters}
    (result : optionalGenericParameters input = .ok parameters next) :
    OptionalGenericParametersParses input.declarativeRemainder parameters
      next.declarativeRemainder :=
  optionalGenericParameters_success_sound result

end Solcore.Test.SyntaxParserGenericParametersSoundnessProperties
