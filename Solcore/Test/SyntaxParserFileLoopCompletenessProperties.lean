import Solcore.Syntax.Parser.TopItemRecoveryCompletenessProperties
import Solcore.Syntax.Parser.FileItemsCompletenessProperties

/-! Compile-time consumers for recovery and exact file-loop prefix handling. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFileLoopCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example := @recoverTopItem_ordinary_success_iff
example := @recoverTopItem_ordinary_reject_iff
example := @parseItems_ordinary_success_iff_of_remainingCount_lt
example := @parseItems_production_ordinary_success_iff

example {input : State} {value : TopItem}
    {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.TopItemRecoveryParses
      input.declarativeRemainder value remainder) :
    ∃ output, recoverTopItem input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  recoverTopItem_ordinary_success_iff.mp parsed

example {input : State} {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.TopItemRecoveryRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, recoverTopItem input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  recoverTopItem_ordinary_reject_iff.mp rejection

example (fuel : Nat) (itemsRev : List TopItem)
    {input : State} (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    {suffix : List TopItem} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.FileItemsOrdinaryParses
      input.declarativeRemainder suffix remainder) :
    ∃ output, parseItems fuel itemsRev input =
      .ok (itemsRev.reverse ++ suffix) output ∧
      output.declarativeRemainder = remainder :=
  (parseItems_ordinary_success_iff_of_remainingCount_lt
    fuel itemsRev inputValid adequate).mp parsed

example (itemsRev : List TopItem)
    {input output : State} (inputValid : input.ValidFor) {suffix : List TopItem}
    (result : parseItems (input.remainingCount + 1) itemsRev input =
      .ok (itemsRev.reverse ++ suffix) output) :
    DeclarativeGrammar.FileItemsOrdinaryParses input.declarativeRemainder suffix
      output.declarativeRemainder :=
  (parseItems_production_ordinary_success_iff itemsRev inputValid).mpr
    ⟨output, result, rfl⟩

example {input : State} (inputValid : input.ValidFor)
    {items : List TopItem} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.FileItemsOrdinaryParses
      input.declarativeRemainder items remainder) :
    ∃ output, parseItems (input.remainingCount + 1) [] input = .ok items output ∧
      output.declarativeRemainder = remainder := by
  simpa using (parseItems_production_ordinary_success_iff [] inputValid).mp parsed

example (earlier latest : TopItem)
    {input : State} (inputValid : input.ValidFor)
    {suffix : List TopItem} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.FileItemsOrdinaryParses
      input.declarativeRemainder suffix remainder) :
    ∃ output, parseItems (input.remainingCount + 1) [latest, earlier] input =
      .ok ([earlier, latest] ++ suffix) output ∧
      output.declarativeRemainder = remainder := by
  simpa using (parseItems_production_ordinary_success_iff
    [latest, earlier] inputValid).mp parsed

end Solcore.Test.SyntaxParserFileLoopCompletenessProperties
