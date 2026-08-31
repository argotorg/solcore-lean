import Solcore.Syntax.Parser.ExpressionFuelContractProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionFuelContractProperties

open Solcore.Syntax.Parser.ExpressionInternals

example := @leftAssociative_fuelTotalityContract
example := @nonAssociative_fuelTotalityContract
example := @expressionUnary_fuelTotalityContract
example := @conditional_fuelTotalityContract

end Solcore.Test.SyntaxParserExpressionFuelContractProperties
