import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDelimitedFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @FuelElementTotalityContract.ne_invariant
example := @afterDelimitedElement_ordinary_of_elementFuel
example := @delimitedWithPolicy_ordinary_of_elementFuel
example := @delimited_ordinary_of_elementFuel
example := @delimited_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserDelimitedFuelTotalityProperties
