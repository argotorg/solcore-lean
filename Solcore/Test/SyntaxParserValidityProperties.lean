import Solcore

/-! External compile consumers for compositional parser validity contracts. -/

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @Reply.ValidFor
example := @Parser.ValidFor
example := @Parser.PreservesTokensOnSuccess
example := @Parser.CursorMonotoneOnSuccess
example := @Parser.pure_preservesTokensOnSuccess
example := @Parser.pure_cursorMonotoneOnSuccess
example := @Parser.bind_preservesTokensOnSuccess
example := @Parser.bind_cursorMonotoneOnSuccess
example := @Parser.orElse_preservesTokensOnSuccess
example := @Parser.orElse_cursorMonotoneOnSuccess
example := @Parser.validFor_of_ok_reject
example := @Parser.pure_validFor
example := @Parser.bind_validFor
example := @Parser.bind_validFor_of_value
example := @Parser.orElse_validFor
example := @Parser.ValidFor.mono
example := @getState_validFor
example := @getState_preservesTokenWindow
example := @getState_preservesTokensOnSuccess
example := @getState_cursorMonotoneOnSuccess
example := @modifyState_validFor
example := @modifyState_preservesTokenWindow
example := @modifyState_preservesTokensOnSuccess
example := @modifyState_cursorMonotoneOnSuccess
example := @emitDiagnostic_reply_validFor
example := @emitDiagnostic_validFor
example := @emitDiagnostic_preservesTokenWindow
example := @emitDiagnostic_preservesTokensOnSuccess
example := @emitDiagnostic_cursorMonotoneOnSuccess
example := @emitFailure_validFor
example := @acceptToken_validFor
example := @keyword_validFor
example := @symbol_validFor
example := @contextual_validFor
example := @rawIdentifier_validFor
example := @identifier_validFor
example := @yulIdentifier_validFor
example := coreLiteral_validFor
example := booleanIdentifier_validFor

end Tests
