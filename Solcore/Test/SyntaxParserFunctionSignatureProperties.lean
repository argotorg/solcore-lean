import Solcore.Syntax.Parser.Signature

/-! External compile consumers for function-signature prerequisites. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := functionParameters_validFor
example := functionParameters_preservesTokenWindow
example := functionParameters_preservesTokensOnSuccess
example := functionParameters_cursorMonotoneOnSuccess
example := functionParameters_startsAtCurrentTokenOnSuccess
example := @optionalFunctionModifier_some_startsAtCurrentTokenOnSuccess
example := @functionSignature_validFor_of_span
example := @functionSignature_span_validOnSuccess
example := @functionSignature_validFor
example := @functionSignature_preservesTokenWindow_of_where
example := @functionSignature_preservesTokensOnSuccess_of_where
example := @functionSignature_cursorMonotoneOnSuccess_of_where
example := @functionSignature_preservesTokenWindow
example := @functionSignature_preservesTokensOnSuccess
example := @functionSignature_cursorMonotoneOnSuccess
example := @functionSignature_startsAtCurrentTokenOnSuccess
example := @SignatureInternals.signatureEnd_where
example := @SignatureInternals.signatureEnd_returns
example := @SignatureInternals.signatureEnd_payable
example := @SignatureInternals.signatureEnd_public
example := @SignatureInternals.signatureEnd_parameters
example := @SignatureInternals.signatureEnd_validFor
example := @functionSignature_keyword_start_le_endOnSuccess
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
