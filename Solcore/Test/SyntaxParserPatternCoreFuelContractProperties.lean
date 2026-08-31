import Solcore.Syntax.Parser.PatternCoreFuelContractProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternCoreFuelContractProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PatternInternals

example := @patternCore_weakValidFor
example := @patternCore_fuelElementTotalityContract

end Solcore.Test.SyntaxParserPatternCoreFuelContractProperties
