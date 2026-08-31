import Solcore.Syntax.Parser.PublicDiagnosticValidityProperties

/-! External consumers for public parse-diagnostic validity. -/

namespace Tests

open Solcore.Syntax.Parser

example := @parseLexed_ok_parseDiagnostics_validFor
example := @parse_ok_parseDiagnostics_validFor

end Tests
