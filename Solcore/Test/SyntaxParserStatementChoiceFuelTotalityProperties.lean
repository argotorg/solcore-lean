import Solcore.Syntax.Parser.Statement.ChoiceFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementChoiceFuelTotalityProperties

open Solcore.Syntax.Parser.TermInternals

example := @FuelStatementTotalityContract.ofTotality
example := @recognizedStatementOrFallback_ordinary_of_fuels
example := @recognizedStatementOrFallback_fuelTotalityContract
example := @recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
example := @stateChoice_fuelTotalityContract
example := @stateChoice_cursor_lt_onSuccess_of_strict

end Solcore.Test.SyntaxParserStatementChoiceFuelTotalityProperties
