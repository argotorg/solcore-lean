import Solcore.Syntax.Parser.Pattern

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternRecoveryTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PatternInternals

example := @recoverPatternAux_exists_ok_of_remainingCount_lt
example := @recoverPatternAux_ordinary_of_remainingCount_lt
example := @recoverPatternAux_ne_invariant_of_remainingCount_lt
example := @recoverPatternAux_production_exists_ok
example := @recoverPatternAux_production_ordinary
example := @recoverPatternAux_production_invariantFreeOnValid
example := @recoverPatternAux_production_ne_invariant

end Solcore.Test.SyntaxParserPatternRecoveryTotalityProperties
