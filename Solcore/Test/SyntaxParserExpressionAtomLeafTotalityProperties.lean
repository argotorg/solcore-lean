import Solcore.Syntax.Parser.Expression.AtomLeafTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionAtomLeafTotalityProperties

open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals

example : ElementTotalityContract expressionName :=
  expressionName_elementTotalityContract

example : Parser.InvariantFreeOnValid literalExpression :=
  literalExpression_invariantFreeOnValid

example : Parser.InvariantFreeOnValid identifierExpression :=
  identifierExpression_invariantFreeOnValid

example : Parser.InvariantFreeOnValid proxyExpression :=
  proxyExpression_invariantFreeOnValid

example : Parser.InvariantFreeOnValid optionalLambdaReturnType :=
  optionalLambdaReturnType_invariantFreeOnValid

end Solcore.Test.SyntaxParserExpressionAtomLeafTotalityProperties
