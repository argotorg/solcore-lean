import Solcore.Syntax.Parser.Signature

/-! External compile consumers for function-signature prerequisites. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := returnClause_validFor
example := returnClause_preservesTokenWindow
example := returnClause_preservesTokensOnSuccess
example := returnClause_cursorMonotoneOnSuccess
example := @returnClause_some_startsAtCurrentTokenOnSuccess
example := functionModifiers_validFor
example := functionModifiers_preservesTokenWindow
example := functionModifiers_preservesTokensOnSuccess
example := functionModifiers_cursorMonotoneOnSuccess

end Tests
