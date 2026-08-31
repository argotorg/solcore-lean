import Solcore

/-! External compile consumers for compositional parser validity contracts. -/

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @Reply.ValidFor
example := @Parser.ValidFor
example := @Parser.validFor_of_ok_reject
example := @Parser.pure_validFor
example := @Parser.bind_validFor
example := @Parser.bind_validFor_of_value
example := @Parser.orElse_validFor
example := @Parser.ValidFor.mono
example := @getState_validFor
example := @modifyState_validFor
example := @emitDiagnostic_reply_validFor
example := @emitDiagnostic_validFor
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
