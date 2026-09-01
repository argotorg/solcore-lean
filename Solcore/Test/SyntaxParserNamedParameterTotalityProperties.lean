import Solcore.Syntax.Parser.NamedParameterTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserNamedParameterTotalityProperties

open Solcore.Syntax.Parser

example := @FunctionParameterInternals.namedParameterCore_invariantFreeOnValid
example := @FunctionParameterInternals.namedParameterCore_cursor_lt_onSuccess
example := @namedParameter_ordinary
example := @namedParameter_invariantFreeOnValid
example := @namedParameter_ne_invariant
example := @namedParameter_cursor_lt_onSuccess
example := @namedParameter_elementTotalityContract

end Solcore.Test.SyntaxParserNamedParameterTotalityProperties
