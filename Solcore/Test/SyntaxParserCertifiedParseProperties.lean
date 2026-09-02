import Solcore.Syntax.Parser.CertifiedParseProperties

/-! External consumers for total parsing with complete output provenance. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCertifiedParseProperties

open Solcore.Syntax.Parser

example := @productionParseLexed_exists_ok_completeOutput_validFor
example := @productionParse_exists_ok_completeOutput_validFor
example := @productionParseLexed_exists_ok_publicSourceFileOrdinary
example := @productionParse_exists_ok_publicSourceFileOrdinary

end Solcore.Test.SyntaxParserCertifiedParseProperties
