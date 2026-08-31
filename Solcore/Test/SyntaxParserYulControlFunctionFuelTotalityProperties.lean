import Solcore.Syntax.Parser.Yul.ControlFunctionFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulControlFunctionFuelTotalityProperties

open Solcore.Syntax.Parser

example := @FuelYulStatementTotalityContract.fuelElementTotalityContract
example := @yulBlockStatement_ordinary_of_statementFuel
example := @yulBlockStatement_ne_invariant_of_statementFuel
example := @yulBlockStatement_cursor_lt_onSuccess
example := @yulBlockStatement_fuelTotalityContract
example := @yulFunctionStatement_ordinary_of_statementFuel
example := @yulFunctionStatement_ne_invariant_of_statementFuel
example := @yulFunctionStatement_cursor_lt_onSuccess
example := @yulFunctionStatement_fuelTotalityContract

end Solcore.Test.SyntaxParserYulControlFunctionFuelTotalityProperties
