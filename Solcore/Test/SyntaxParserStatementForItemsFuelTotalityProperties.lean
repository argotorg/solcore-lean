import Solcore.Syntax.Parser.Statement.ForItemsFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementForItemsFuelTotalityProperties

open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ControlInternals

example := @forItemsTail_ordinary_of_itemFuel
example := @forItemsTail_ne_invariant_of_itemFuel
example := @forItems_ordinary_of_itemFuel
example := @forItems_ne_invariant_of_itemFuel
example := @forItems_fuelTotalityContract

end Solcore.Test.SyntaxParserStatementForItemsFuelTotalityProperties
