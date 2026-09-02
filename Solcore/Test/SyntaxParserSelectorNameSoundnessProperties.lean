import Solcore.Syntax.Parser.SelectorNameOrdinaryOutcomeSoundnessProperties

/-! External consumers for selector-name grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSelectorNameSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @SelectorOperatorSymbol
example := @SelectorOperatorPartsParses
example := @SelectorOperatorPartAbsentAt
example := @MaximalSelectorOperatorPartsParses
example := @OperatorSelectorParses
example := @SelectorNameParses
example := @SelectorNameOrdinaryParses
example := @SelectorNameRejects
example := @selectorNameDeterministicOutcomeSpec
example := @operatorPart?_eq_some_iff
example := @operatorSelector_success_sound
example := @selectorName_success_sound
example := @selectorName_success_sound_and_validFor
example := @selectorName_success_ordinaryOutcome_sound
example := @selectorName_reject_ordinaryOutcome_sound
example := @selectorName_ordinaryOutcome_sound
example := @selectorName_ordinaryOutcomeSpec

example {kind : TokenKind} {spelling : String} :
    operatorPart? kind = some spelling ↔
      ∃ symbol,
        kind = .symbol symbol ∧
        SelectorOperatorSymbol symbol ∧
        spelling = symbol.spelling :=
  operatorPart?_eq_some_iff

example (context : ParseContext) {input next : State}
    {selector : SelectorName}
    (result : selectorName context input = .ok selector next) :
    SelectorNameParses input.declarativeRemainder selector
      next.declarativeRemainder :=
  selectorName_success_sound context result

example (context : ParseContext) {input next : State}
    {selector : SelectorName} (inputValid : input.ValidFor)
    (result : selectorName context input = .ok selector next) :
    SelectorNameParses input.declarativeRemainder selector
        next.declarativeRemainder ∧
      selector.ValidFor input.file :=
  selectorName_success_sound_and_validFor context inputValid result

end Solcore.Test.SyntaxParserSelectorNameSoundnessProperties
