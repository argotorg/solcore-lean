import Solcore.Syntax.Parser.Yul.StatementChoiceFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulStatementChoiceFuelTotalityProperties

open Solcore.Syntax.Parser

example := @recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
example := @stateChoice_fuelTotalityContract
example := @stateChoice_cursor_lt_onSuccess_of_strict
example := @orElse_fuelTotalityContract
example := @orElse_cursor_lt_onSuccess_of_strict

end Solcore.Test.SyntaxParserYulStatementChoiceFuelTotalityProperties
