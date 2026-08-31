import Solcore.Syntax.Parser.Yul.ExpressionRecursiveTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulExpressionRecursiveTotalityProperties

open Solcore.Syntax.Parser

example := @YulExpressionInternals.layer_cursor_lt_onSuccess
example := @YulExpressionInternals.withFuel_cursor_lt_onSuccess
example := @YulExpressionInternals.withFuel_fuelElementTotalityContract
example := @YulExpressionInternals.withFuel_ordinary_of_remainingCount_lt
example := @YulExpressionInternals.withFuel_ne_invariant_of_remainingCount_lt
example := @yulExpression_invariantFreeOnValid
example := @yulExpression_ne_invariant
example := @yulExpression_cursor_lt_onSuccess
example := @yulExpression_elementTotalityContract

example (input : State) (inputValid : input.ValidFor) :
    (∃ expression next, yulExpression input = .ok expression next) ∨
    (∃ failure next, yulExpression input = .reject failure next) :=
  yulExpression_invariantFreeOnValid input inputValid

end Solcore.Test.SyntaxParserYulExpressionRecursiveTotalityProperties
