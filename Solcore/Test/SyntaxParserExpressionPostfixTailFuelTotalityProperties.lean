import Solcore.Syntax.Parser.Expression.PostfixTailFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionPostfixTailFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @postfixTail_ordinary_of_fuel
example := @postfixTail_ne_invariant_of_fuel
example := @postfixTail_production_ordinary

end Solcore.Test.SyntaxParserExpressionPostfixTailFuelTotalityProperties
