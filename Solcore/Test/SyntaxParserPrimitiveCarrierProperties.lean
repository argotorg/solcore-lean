import Solcore.Syntax.Parser.PrimitiveCarrierProperties

/-! External consumers for primitive parser token-carrier laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @acceptToken_preservesTokensOnSuccess
example := @keyword_preservesTokensOnSuccess
example := @symbol_preservesTokensOnSuccess
example := @contextual_preservesTokensOnSuccess
example := @rawIdentifier_ok_state_shape
example := @rawIdentifier_preservesTokensOnSuccess
example := @identifier_preservesTokensOnSuccess
example := @yulIdentifier_ok_state_shape
example := @yulIdentifier_preservesTokensOnSuccess

end Tests
