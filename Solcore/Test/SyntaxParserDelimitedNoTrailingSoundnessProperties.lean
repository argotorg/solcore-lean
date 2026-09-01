import Solcore.Syntax.Parser.DelimitedNoTrailingSoundnessProperties

/-! External consumers for no-trailing delimited-list soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDelimitedNoTrailingSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @NoTrailingDelimitedTailParses
example := @NonemptyNoTrailingDelimitedListParses
example := @delimitedNoTrailing_nonempty_success_sound

example {α : Type} (opening closing : Symbol) (element : Parser α)
    (elementParses : Remainder → α → Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList α}
    (result : delimitedNoTrailing opening closing false element context phase
      input = .ok values next) :
    NonemptyNoTrailingDelimitedListParses opening closing elementParses
      input.declarativeRemainder values next.declarativeRemainder :=
  delimitedNoTrailing_nonempty_success_sound opening closing element
    elementParses context phase elementSound elementShape result

end Solcore.Test.SyntaxParserDelimitedNoTrailingSoundnessProperties
