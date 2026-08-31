import Solcore.Syntax.Parser.Yul.ControlForFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulControlForFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulForStatement_ordinary_of_statementFuel
example := @yulForStatement_ne_invariant_of_statementFuel
example := @yulForStatement_cursor_lt_onSuccess
example := @yulForStatement_fuelElementTotalityContract
example := @yulForStatement_fuelTotalityContract

example (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel) :
    FuelElementTotalityContract (yulForStatement statement)
      (statementFuel + 2) :=
  yulForStatement_fuelElementTotalityContract statement statementFuel
    contract

end Solcore.Test.SyntaxParserYulControlForFuelTotalityProperties
