import Solcore.Syntax.Parser.Statement.ControlBlockFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementControlBlockFuelTotalityProperties

open Solcore.Syntax.Parser

example := @blockStatement_ordinary_of_statementFuel
example := @blockStatement_ne_invariant_of_statementFuel
example := @blockStatement_fuelTotalityContract
example := @whileStatement_ordinary_of_fuels
example := @whileStatement_ne_invariant_of_fuels
example := @whileStatement_fuelTotalityContract

end Solcore.Test.SyntaxParserStatementControlBlockFuelTotalityProperties
