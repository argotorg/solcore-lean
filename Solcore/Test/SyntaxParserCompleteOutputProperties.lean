import Solcore.Syntax.Parser.CompleteOutputProperties

/-! External consumers for complete public parser output validity. -/

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @ParseOutput.CanonicalValidFor
example := @parseLexed_ok_completeOutput_validFor
example := @parse_ok_completeOutput_validFor

end Tests
