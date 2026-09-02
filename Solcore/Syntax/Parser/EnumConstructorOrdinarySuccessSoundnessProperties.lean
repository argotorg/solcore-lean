import Solcore.Syntax.DeclarativeEnumConstructorOutcomeGrammar
import Solcore.Syntax.Parser.EnumConstructorSoundnessProperties

/-! Ordinary-success bridges for enum constructors and tuple payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

/-- Every successful optional enum-constructor payload follows the public Core
type ordinary grammar with its exact output remainder. -/
theorem enumConstructorFields_success_ordinaryOutcome_sound
    {input output : State} {fields : Option (DelimitedList TypeExpr)}
    (result : enumConstructorFields input = .ok fields output) :
    DeclarativeGrammar.OptionalEnumConstructorFieldsOrdinaryParses
      input.declarativeRemainder fields output.declarativeRemainder :=
  enumConstructorFields_success_sound result

/-- Every successful enum constructor records its exact name, optional tuple
payload, AST span, empty leading trivia, and output remainder. -/
theorem enumConstructor_success_ordinaryOutcome_sound
    {input output : State} {constructor : EnumConstructor}
    (result : enumConstructor input = .ok constructor output) :
    DeclarativeGrammar.EnumConstructorOrdinaryParses
      input.declarativeRemainder constructor output.declarativeRemainder :=
  enumConstructor_success_sound result

end Solcore.Syntax.Parser.EnumInternals
