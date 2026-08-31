import Solcore.Syntax.Parser.Statement.ControlForFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementControlForFuelTotalityProperties

open Solcore.Syntax.Parser

example := @forStatement_ordinary_of_fuels
example := @forStatement_ne_invariant_of_fuels

end Solcore.Test.SyntaxParserStatementControlForFuelTotalityProperties
