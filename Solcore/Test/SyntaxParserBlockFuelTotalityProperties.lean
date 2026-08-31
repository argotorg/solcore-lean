import Solcore.Syntax.Parser.BlockFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserBlockFuelTotalityProperties

open Solcore.Syntax.Parser

example := @coreBlock_ordinary_of_statementFuel
example := @coreBlock_ne_invariant_of_statementFuel
example := @isolatedCoreBlock_ordinary_of_statementFuel
example := @isolatedCoreBlock_ne_invariant_of_statementFuel
example := @coreBlock_fuelTotalityContract
example := @isolatedCoreBlock_fuelTotalityContract

end Solcore.Test.SyntaxParserBlockFuelTotalityProperties
