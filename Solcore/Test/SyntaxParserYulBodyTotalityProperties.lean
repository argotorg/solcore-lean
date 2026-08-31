import Solcore.Syntax.Parser.Yul.BodyTotalityProperties

/-! Compile-time consumers for public inline-Yul body totality. -/

namespace Solcore.Test.SyntaxParserYulBodyTotalityProperties

open Solcore.Syntax.Parser

example := @yulStatement_elementTotalityContract
example := @yulBody_ordinary
example := @yulBody_invariantFreeOnValid
example := @yulBody_ne_invariant
example := @yulBody_cursor_lt_onSuccess
example := @yulBody_elementTotalityContract

end Solcore.Test.SyntaxParserYulBodyTotalityProperties
