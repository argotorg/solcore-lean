import Solcore.Syntax.Parser.Yul.StatementRecursiveFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulStatementRecursiveFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulStatementWithFuel_cursor_lt_onSuccess
example := @yulStatementWithFuel_fuelTotalityContract
example := @yulStatement_ordinary
example := @yulStatement_invariantFreeOnValid
example := @yulStatement_ne_invariant
example := @yulStatement_cursor_lt_onSuccess
example := @yulStatement_totalityContract

example (fuel : Nat) :
    FuelYulStatementTotalityContract (yulStatementWithFuel fuel) fuel :=
  yulStatementWithFuel_fuelTotalityContract fuel

end Solcore.Test.SyntaxParserYulStatementRecursiveFuelTotalityProperties
