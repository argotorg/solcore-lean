import Solcore.Syntax.Parser.TypeNamedTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeNamedTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseNamedTypeArguments nested input ≠ .invariant error :=
  parseNamedTypeArguments_ne_invariant nested contract input inputValid error

example (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor) :
    (∃ value next, parseNamedType nested input = .ok value next) ∨
    (∃ failure next, parseNamedType nested input = .reject failure next) :=
  parseNamedType_ordinary nested contract input inputValid

end Solcore.Test.SyntaxParserTypeNamedTotalityProperties
