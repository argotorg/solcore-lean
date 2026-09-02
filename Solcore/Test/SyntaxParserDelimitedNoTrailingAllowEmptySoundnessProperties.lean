import Solcore.Syntax.DeclarativeDelimitedNoTrailingExactnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingAllowEmptySoundnessProperties

/-! External consumers for allow-empty no-trailing-list grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDelimitedNoTrailingAllowEmptySoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @NoTrailingDelimitedListParses
example := @NoTrailingDelimitedListParses.value_unique
example := @noTrailingDelimitedListExactOutcomeSpec
example := @delimitedNoTrailing_allowEmpty_success_sound

example {α : Type} (opening closing : Symbol) (element : Parser α)
    (elementParses : Remainder → α → Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList α}
    (result : delimitedNoTrailing opening closing true element context phase
      input = .ok values next) :
    NoTrailingDelimitedListParses opening closing elementParses
      input.declarativeRemainder values next.declarativeRemainder :=
  delimitedNoTrailing_allowEmpty_success_sound opening closing element
    elementParses context phase elementSound elementShape result

end Solcore.Test.SyntaxParserDelimitedNoTrailingAllowEmptySoundnessProperties
