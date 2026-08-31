import Solcore.Syntax.Parser.Statement.ControlIfFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementControlIfFuelTotalityProperties

open Solcore.Syntax.Parser

example := @ControlInternals.optionalElseBody_ordinary_of_blockFuel
example := @ifStatement_ordinary_of_fuels
example := @ifStatement_ne_invariant_of_fuels
example := @ifStatement_fuelTotalityContract

end Solcore.Test.SyntaxParserStatementControlIfFuelTotalityProperties
