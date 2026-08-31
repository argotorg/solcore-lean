import Solcore.Syntax.Parser.PatternCoreFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternCoreFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PatternInternals

example (nested : Parser Pattern) (expression : Parser Expr)
    (nestedFuel expressionFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (expressionContract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (expressionAdequate : input.remainingCount < expressionFuel + 1)
    (error : ParserInvariantError) :
    patternCore nested expression input ≠ .invariant error :=
  patternCore_ne_invariant_of_elementFuel nested expression nestedFuel
    expressionFuel nestedContract expressionContract input inputValid
    nestedAdequate expressionAdequate error

end Solcore.Test.SyntaxParserPatternCoreFuelTotalityProperties
