import Solcore.Syntax.Parser.DelimitedSoundnessProperties
import Solcore.Syntax.Parser.SelectorNameSoundnessProperties

/-! External consumers for declarative delimited-list soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDelimitedSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TrailingDelimitedTailParses
example := @NonemptyTrailingDelimitedListParses
example := @delimited_nonempty_trailing_success_sound

example {α : Type} (opening closing : Symbol) (element : Parser α)
    (elementParses : Remainder → α → Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList α}
    (result : delimited opening closing false element context phase input =
      .ok values next) :
    NonemptyTrailingDelimitedListParses opening closing elementParses
      input.declarativeRemainder values next.declarativeRemainder :=
  delimited_nonempty_trailing_success_sound opening closing element
    elementParses context phase elementSound elementShape result

example {input next : State} {values : DelimitedList SelectorName}
    (result : delimited .leftBrace .rightBrace false
      (selectorName .importDecl) .importDecl .topLevel input =
        .ok values next) :
    NonemptyTrailingDelimitedListParses .leftBrace .rightBrace
      SelectorNameParses input.declarativeRemainder values
      next.declarativeRemainder :=
  delimited_nonempty_trailing_success_sound .leftBrace .rightBrace
    (selectorName .importDecl) SelectorNameParses .importDecl .topLevel
    (selectorName_success_sound .importDecl)
    (selectorName_preservesTokenWindow .importDecl) result

end Solcore.Test.SyntaxParserDelimitedSoundnessProperties
