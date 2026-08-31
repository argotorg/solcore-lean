import Solcore.Syntax.Parser.TypeStrictProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeStrictProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @parseNamedType_cursor_lt_onSuccess
example := @parseMappingType_cursor_lt_onSuccess
example := @parseComptimeType_cursor_lt_onSuccess
example := @parseProxyType_cursor_lt_onSuccess
example := @parseTupleType_cursor_lt_onSuccess
example := @parseFunctionType_cursor_lt_onSuccess
example := @typeExprWithFuel_cursor_lt_onSuccess
example := @typeExpr_cursor_lt_onSuccess

end Solcore.Test.SyntaxParserTypeStrictProperties
