import Solcore.Syntax.Parser.Yul.BlockFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulBlockFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulBlockItems_ordinary_of_statementFuel
example := @yulBlockItems_ne_invariant_of_statementFuel
example := @yulBlock_ordinary_of_statementFuel
example := @yulBlock_ne_invariant_of_statementFuel
example := @yulBlock_fuelElementTotalityContract

example (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel) :
    FuelElementTotalityContract (yulBlock statement) (statementFuel + 1) :=
  yulBlock_fuelElementTotalityContract statement statementFuel contract

end Solcore.Test.SyntaxParserYulBlockFuelTotalityProperties
