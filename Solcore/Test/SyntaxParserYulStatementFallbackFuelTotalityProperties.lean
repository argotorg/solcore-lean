import Solcore.Syntax.Parser.Yul.StatementFallbackFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulStatementFallbackFuelTotalityProperties

open Solcore.Syntax.Parser

example := @FuelYulStatementTotalityContract.ne_invariant
example := @FuelYulStatementTotalityContract.ofTotality
example := @recognizedYulStatementOrFallback_ordinary_of_fuels
example := @recognizedYulStatementOrFallback_fuelTotalityContract
example := @optionalYulSemicolon_ordinary
example := @yulStatementTerminated_ordinary_of_coreFuel
example := @yulStatementTerminated_fuelTotalityContract

end Solcore.Test.SyntaxParserYulStatementFallbackFuelTotalityProperties
