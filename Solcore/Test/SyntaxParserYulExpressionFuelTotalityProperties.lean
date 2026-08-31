import Solcore.Syntax.Parser.Yul.ExpressionFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulExpressionFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @optionalYulCallArguments_ordinary_of_elementFuel
example := @optionalYulCallArguments_ne_invariant_of_elementFuel
example := @yulExpressionCore_ordinary_of_elementFuel
example := @yulExpressionCore_ne_invariant_of_elementFuel
example := @YulExpressionInternals.recoverAux_exists_ok_of_remainingCount_lt
example := @YulExpressionInternals.recoverAux_production_exists_ok
example := @YulExpressionInternals.recoverAux_ne_invariant_of_remainingCount_lt
example := @YulExpressionInternals.layer_ordinary_of_elementFuel
example := @YulExpressionInternals.layer_ne_invariant_of_elementFuel

example (nested : Parser YulExpr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next,
      YulExpressionInternals.layer nested input = .ok expression next) ∨
    (∃ failure next,
      YulExpressionInternals.layer nested input = .reject failure next) :=
  YulExpressionInternals.layer_ordinary_of_elementFuel nested nestedFuel
    contract input inputValid adequate

end Solcore.Test.SyntaxParserYulExpressionFuelTotalityProperties
