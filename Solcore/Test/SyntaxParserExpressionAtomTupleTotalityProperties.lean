import Solcore.Syntax.Parser.Expression.AtomTupleTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionAtomTupleTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @closeTuple_invariantFreeOnValid
example := @tupleTail_ordinary_of_elementFuel
example := @tupleTail_ne_invariant_of_elementFuel
example := @tupleTail_production_ordinary_of_elementFuel
example := @tupleTail_production_ne_invariant_of_elementFuel
example := @parenthesized_ordinary_of_elementFuel
example := @parenthesized_ne_invariant_of_elementFuel

example (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, parenthesized nested input = .ok value next) ∨
      (∃ failure next,
        parenthesized nested input = .reject failure next) :=
  parenthesized_ordinary_of_elementFuel nested nestedFuel contract input
    inputValid adequate

end Solcore.Test.SyntaxParserExpressionAtomTupleTotalityProperties
