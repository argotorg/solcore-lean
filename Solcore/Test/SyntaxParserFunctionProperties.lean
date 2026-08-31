import Solcore.Syntax.Parser.FunctionProperties

/-! External compile consumers for complete-function state contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax.Parser

example := @functionDecl_preservesTokenWindow_of_block
example := @functionDecl_preservesTokensOnSuccess_of_block
example := @functionDecl_cursorMonotoneOnSuccess_of_block
example := @functionDecl_startsAtCurrentTokenOnSuccess

end Tests
