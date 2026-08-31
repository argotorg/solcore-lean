import Solcore.Syntax.Parser.FunctionProperties

/-! External compile consumers for complete-function state contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax.Parser

example := @FunctionInternals.block_startsAtCurrentTokenOnSuccess
example := @FunctionInternals.functionSignature_cursor_lt_onSuccess
example := @functionDecl_span_validOnSuccess
example := @functionDecl_validFor_of_span
example := @functionDecl_validFor
example := @functionDecl_preservesTokenWindow_of_block
example := @functionDecl_preservesTokensOnSuccess_of_block
example := @functionDecl_cursorMonotoneOnSuccess_of_block
example := @functionDecl_startsAtCurrentTokenOnSuccess

end Tests
