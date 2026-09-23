import Solcore.Syntax.Parser.Pattern

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternLeafFuelTotalityProperties

open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PatternInternals

example := @comptimePattern_ordinary_of_elementFuel
example := @comptimePattern_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserPatternLeafFuelTotalityProperties
