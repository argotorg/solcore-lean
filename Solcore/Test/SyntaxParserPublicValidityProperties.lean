import Solcore.Syntax.Parser.PublicValidityProperties

/-! External consumers for public parsed-file validity. -/

namespace Tests

open Solcore.Syntax.Parser

example := @CanonicalParsedFileValid
example := @parseLexed_ok_parsed_validFor
example := @parse_ok_parsed_validFor

end Tests
