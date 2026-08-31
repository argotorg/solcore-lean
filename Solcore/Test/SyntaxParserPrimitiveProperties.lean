import Solcore

/-! External compile consumers for primitive parser provenance laws. -/

namespace Tests

open Solcore.Syntax.Parser

example := @rejectAt_reject_validFor
example := @acceptToken_ok_validFor
example := @acceptToken_reject_validFor
example := @rawIdentifier_ok_validFor
example := @rawIdentifier_reject_validFor
example := @identifier_ok_validFor
example := @identifier_reject_validFor
example := @yulIdentifier_ok_validFor
example := @yulIdentifier_reject_validFor
example := @coreLiteral_ok_validFor
example := @coreLiteral_reject_validFor
example := @booleanIdentifier_ok_validFor
example := @booleanIdentifier_reject_validFor

end Tests
