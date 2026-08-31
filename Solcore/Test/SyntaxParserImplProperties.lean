import Solcore.Syntax.Parser.ImplProperties

/-! External compile consumers for implementation parser state contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax.Parser

example := @ImplInternals.requireImplArguments_preservesTokenWindow
example := @ImplInternals.implMethod_preservesTokenWindow_of_block
example := @ImplInternals.implMethods_preservesTokenWindow_of_block
example := @ImplInternals.implBody_preservesTokenWindow_of_block
example := @ImplInternals.implMethods_cursorMonotoneOnSuccess
example := @ImplInternals.implBody_cursorMonotoneOnSuccess

end Tests
