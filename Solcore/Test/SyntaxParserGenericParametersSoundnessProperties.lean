import Solcore.Syntax.Parser.GenericParametersOrdinaryRejectionSoundnessProperties

/-! External consumers for exact generic-parameter outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserGenericParametersSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @GenericParametersParses
example := @GenericParametersRejects
example := @genericParametersDeterministicOutcomeSpec
example := @OptionalGenericParametersParses
example := @OptionalGenericParametersRejects
example := @optionalGenericParametersDeterministicOutcomeSpec
example := @requireGenericParameters_success_shape
example := @genericParameters_success_sound
example := @genericParameters_success_sound_and_validFor
example := @optionalGenericParameters_success_sound
example := @optionalGenericParameters_success_sound_and_validFor
example := @genericParameters_reject_sound
example := @genericParameters_ordinaryOutcome_sound
example := @optionalGenericParameters_reject_sound
example := @optionalGenericParameters_ordinaryOutcome_sound

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

example {input rejected : State} {failure : Failure}
    (result : genericParameters input = .reject failure rejected) :
    GenericParametersRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  genericParameters_reject_sound result

example {input rejected : State} {failure : Failure}
    (result : optionalGenericParameters input = .reject failure rejected) :
    OptionalGenericParametersRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  optionalGenericParameters_reject_sound result

end Solcore.Test.SyntaxParserGenericParametersSoundnessProperties
