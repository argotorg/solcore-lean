import Solcore.Syntax.Parser.PatternQualifiedFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternQualifiedFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PatternInternals

example (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    qualifiedPattern nested input ≠ .invariant error :=
  qualifiedPattern_ne_invariant_of_elementFuel nested nestedFuel contract
    input inputValid adequate error

end Solcore.Test.SyntaxParserPatternQualifiedFuelTotalityProperties
