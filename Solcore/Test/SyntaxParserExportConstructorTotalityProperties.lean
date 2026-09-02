import Solcore.Syntax.Parser.ConstructorSelectionOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ExportConstructorTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportConstructorTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExportInternals

example := @ConstructorSelectionOrdinaryParses
example := @ConstructorSelectionRejects
example := @constructorSelectionDeterministicOutcomeSpec
example := @constructorSelection_success_ordinaryOutcome_sound
example := @constructorSelection_reject_ordinaryOutcome_sound
example := @constructorSelection_ordinaryOutcome_sound
example := @constructorSelection_ordinaryOutcomeSpec

example : Parser.InvariantFreeOnValid constructorSelection :=
  constructorSelection_invariantFreeOnValid

example (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    constructorSelection input ≠ .invariant error :=
  constructorSelection_ne_invariant input inputValid error

end Solcore.Test.SyntaxParserExportConstructorTotalityProperties
