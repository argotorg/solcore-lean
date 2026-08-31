import Solcore.Syntax.Parser.Yul.ControlIfFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulControlIfFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulIfStatement_ordinary_of_statementFuel
example := @yulIfStatement_ne_invariant_of_statementFuel
example := @yulIfStatement_cursor_lt_onSuccess
example := @yulIfStatement_fuelElementTotalityContract
example := @yulIfStatement_fuelTotalityContract

example (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel) :
    FuelElementTotalityContract (yulIfStatement statement)
      (statementFuel + 3) :=
  yulIfStatement_fuelElementTotalityContract statement statementFuel contract

end Solcore.Test.SyntaxParserYulControlIfFuelTotalityProperties
