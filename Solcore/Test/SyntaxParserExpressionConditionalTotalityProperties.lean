import Solcore.Syntax.Parser.ExpressionConditionalTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionConditionalTotalityProperties

open Solcore.Syntax.Parser.ExpressionInternals

example := @conditionalTail_ordinary_of_fuels
example := @conditionalTail_ne_invariant_of_fuels
example := @conditional_ordinary_of_elementFuels
example := @conditional_ne_invariant_of_elementFuels

end Solcore.Test.SyntaxParserExpressionConditionalTotalityProperties
