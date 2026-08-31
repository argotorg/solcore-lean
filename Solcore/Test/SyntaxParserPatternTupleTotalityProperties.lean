import Solcore.Syntax.Parser.PatternTupleTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternTupleTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PatternInternals

example := @closePatternTuple_invariantFreeOnValid
example := @patternTupleTail_ordinary_of_elementFuel
example := @patternTupleTail_ne_invariant_of_elementFuel
example := @patternTupleTail_production_ordinary_of_elementFuel
example := @patternTupleTail_production_ne_invariant_of_elementFuel
example := @parenthesizedPattern_ordinary_of_elementFuel
example := @parenthesizedPattern_ne_invariant_of_elementFuel

example (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, parenthesizedPattern nested input = .ok value next) ∨
      (∃ failure next,
        parenthesizedPattern nested input = .reject failure next) :=
  parenthesizedPattern_ordinary_of_elementFuel nested nestedFuel contract input
    inputValid adequate

end Solcore.Test.SyntaxParserPatternTupleTotalityProperties
