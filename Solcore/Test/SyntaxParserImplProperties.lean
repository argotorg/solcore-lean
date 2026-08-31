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
example := @ImplInternals.implDefaultMarker_preservesTokenWindow
example := @ImplInternals.implDefaultMarker_preservesTokensOnSuccess
example := @ImplInternals.implDefaultMarker_some_startsAtCurrentTokenOnSuccess
example := @ImplInternals.implDeclAfterDefault_preservesTokenWindow_of_block
example := @ImplInternals.implDeclAfterDefault_preservesTokensOnSuccess_of_block
example := @ImplInternals.implDeclAfterDefault_cursor_lt_onSuccess
example := @ImplInternals.implDeclAfterDefault_startOnSuccess
example := @implDecl_preservesTokenWindow_of_block
example := @implDecl_preservesTokensOnSuccess_of_block
example := @implDecl_cursor_lt_onSuccess
example := @implDecl_cursorMonotoneOnSuccess
example := @implDecl_startsAtCurrentTokenOnSuccess
example := @ImplInternals.ImplBody.ValidFor
example := @ImplInternals.requireImplArguments_reply_validFor
example := @ImplInternals.implMethod_validFor
example := @ImplInternals.implMethods_validFor
example := @ImplInternals.implBody_validFor
example := @ImplInternals.implBody_startsAtCurrentTokenOnSuccess
example := @ImplInternals.implDefaultMarker_validFor
example := @implDecl_validFor

end Tests
