import Solcore.Syntax.Parser.Expression.LambdaTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionLambdaTotalityProperties

open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @lambdaExpression_invariantFreeOnValid
example := @lambdaExpression_ne_invariant
example := @lambdaExpression_elementTotalityContract

end Solcore.Test.SyntaxParserExpressionLambdaTotalityProperties
