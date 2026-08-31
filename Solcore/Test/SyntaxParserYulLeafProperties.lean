import Solcore.Syntax.Parser.Yul.LeafProperties

set_option autoImplicit false

namespace Tests
open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulName_validFor
example := @yulLiteral_validFor
example := @yulName_preservesTokensOnSuccess
example := @yulLiteral_preservesTokensOnSuccess
example := @yulName_cursorMonotoneOnSuccess
example := @yulLiteral_cursorMonotoneOnSuccess
example := @yulName_ok_state_shape
example := @yulLiteral_ok_state_shape
end Tests
