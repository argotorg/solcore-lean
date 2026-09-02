import Solcore.Syntax.DeclarativeEnumBodyOutcomeGrammar
import Solcore.Syntax.Parser.EnumBodySoundnessProperties

/-! Ordinary-success bridge for canonical enum bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

/-- Every successful enum body records its exact cover span, constructor list,
and final remainder in the single-output ordinary relation. -/
theorem enumBody_success_ordinaryOutcome_sound
    {input output : State} {body : EnumBody}
    (result : enumBody input = .ok body output) :
    DeclarativeGrammar.EnumBodyOrdinaryOutcomeParses
      input.declarativeRemainder (body.span, body.constructors)
        output.declarativeRemainder :=
  enumBody_success_sound result

end Solcore.Syntax.Parser.EnumInternals
