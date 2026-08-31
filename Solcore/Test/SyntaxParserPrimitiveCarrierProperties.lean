import Solcore.Syntax.Parser.PrimitiveCarrierProperties

/-! External consumers for primitive parser token-carrier laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @acceptToken_preservesTokensOnSuccess
example := @acceptToken_cursor_lt_onSuccess
example := @acceptToken_cursorMonotoneOnSuccess
example := @keyword_preservesTokensOnSuccess
example := @keyword_cursorMonotoneOnSuccess
example := @symbol_preservesTokensOnSuccess
example := @symbol_cursorMonotoneOnSuccess
example := @contextual_preservesTokensOnSuccess
example := @contextual_cursorMonotoneOnSuccess
example := @rawIdentifier_ok_state_shape
example := @rawIdentifier_preservesTokensOnSuccess
example := @rawIdentifier_cursorMonotoneOnSuccess
example := @identifier_preservesTokensOnSuccess
example := @identifier_cursorMonotoneOnSuccess
example := @yulIdentifier_ok_state_shape
example := @yulIdentifier_preservesTokensOnSuccess
example := @yulIdentifier_cursorMonotoneOnSuccess

end Tests
