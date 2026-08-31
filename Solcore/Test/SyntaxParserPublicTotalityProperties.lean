import Solcore.Syntax.Parser.PublicTotalityProperties

/-! External consumers for conditional public parser totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @parseLexed_exists_ok_of_validFor
example := @parseLexed_ne_error_of_validFor
example := @parse_exists_ok
example := @parse_ne_error

end Tests
