import Solcore.Syntax.Parser.TypeFunctionFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeFunctionFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example :=
  @TypeFunctionInternals.parseFunctionReturns_ordinary_of_elementFuel
example :=
  @TypeFunctionInternals.parseFunctionReturns_ne_invariant_of_elementFuel
example := @parseFunctionType_ordinary_of_elementFuel
example := @parseFunctionType_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserTypeFunctionFuelTotalityProperties
