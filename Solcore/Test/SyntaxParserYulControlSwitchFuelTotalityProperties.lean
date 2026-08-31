import Solcore.Syntax.Parser.Yul.ControlSwitchFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulControlSwitchFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @YulControl.FuelParserTotalityContract.ne_invariant
example := @yulCase_ordinary_of_statementFuel
example := @yulCase_ne_invariant_of_statementFuel
example := @yulCase_fuelElementTotalityContract
example := @yulCases_ordinary_of_fuels
example := @yulCases_ne_invariant_of_fuels
example := @yulCases_fuelTotalityContract

end Solcore.Test.SyntaxParserYulControlSwitchFuelTotalityProperties
