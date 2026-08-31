import Solcore.Syntax.Parser.TypeFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @typeExprWithFuel_ordinary_of_remainingCount_lt
example := @typeExprWithFuel_ne_invariant_of_remainingCount_lt
example := @typeExpr_invariantFreeOnValid
example := @typeExpr_ne_invariant
example := @typeExpr_elementTotalityContract

example : Parser.InvariantFreeOnValid typeExpr :=
  typeExpr_invariantFreeOnValid

end Solcore.Test.SyntaxParserTypeFuelTotalityProperties
