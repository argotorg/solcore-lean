import Solcore.Syntax.Parser.PatternLayerFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternLayerFuelTotalityProperties

open Solcore.Syntax.Parser.PatternInternals

example := @patternLayer_ordinary_of_elementFuel
example := @patternLayer_ne_invariant_of_elementFuel
example := @patternLayer_cursor_lt_onSuccess
example := @patternLayer_fuelElementTotalityContract

end Solcore.Test.SyntaxParserPatternLayerFuelTotalityProperties
