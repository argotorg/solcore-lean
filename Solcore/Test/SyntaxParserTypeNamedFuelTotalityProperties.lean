import Solcore.Syntax.Parser.TypeNamedFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeNamedFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @parseNamedTypeArguments_ordinary_of_elementFuel
example := @parseNamedTypeArguments_ne_invariant_of_elementFuel
example := @parseNamedType_ordinary_of_elementFuel
example := @parseNamedType_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserTypeNamedFuelTotalityProperties
