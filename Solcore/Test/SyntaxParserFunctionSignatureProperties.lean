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

end Tests
