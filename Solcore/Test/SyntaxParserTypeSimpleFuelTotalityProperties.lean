import Solcore.Syntax.Parser.TypeSimpleFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeSimpleFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @parseMappingType_ordinary_of_elementFuel
example := @parseMappingType_ne_invariant_of_elementFuel
example := @parseComptimeType_ordinary_of_elementFuel
example := @parseComptimeType_ne_invariant_of_elementFuel
example := @parseProxyType_ordinary_of_elementFuel
example := @parseProxyType_ne_invariant_of_elementFuel
example := @parseTupleType_ordinary_of_elementFuel
example := @parseTupleType_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserTypeSimpleFuelTotalityProperties
