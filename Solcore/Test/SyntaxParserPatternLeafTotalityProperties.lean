import Solcore.Syntax.Parser.Pattern

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternLeafTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PatternInternals

example : Parser.Ordinary wildcardPattern := wildcardPattern_ordinary
example : ElementTotalityContract patternName :=
  patternName_elementTotalityContract

example (expression : Parser Expr)
    (contract : ElementTotalityContract expression) :
    Parser.InvariantFreeOnValid (comptimePattern expression) :=
  comptimePattern_invariantFreeOnValid expression contract

end Solcore.Test.SyntaxParserPatternLeafTotalityProperties
