import Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties

/-! External consumers for allow-empty trailing-list grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDelimitedAllowEmptySoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TrailingDelimitedListParses
example := @delimited_allowEmpty_trailing_success_sound

example {α : Type} (opening closing : Symbol) (element : Parser α)
    (elementParses : Remainder → α → Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList α}
    (result : delimited opening closing true element context phase input =
      .ok values next) :
    TrailingDelimitedListParses opening closing elementParses
      input.declarativeRemainder values next.declarativeRemainder :=
  delimited_allowEmpty_trailing_success_sound opening closing element
    elementParses context phase elementSound elementShape result

end Solcore.Test.SyntaxParserDelimitedAllowEmptySoundnessProperties
