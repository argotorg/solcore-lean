import Solcore.Syntax.Parser.TypeFunctionTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeFunctionTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.TypeFunctionInternals

example (nested : Parser TypeExpr) (contract : ElementTotalityContract nested) :
    Parser.InvariantFreeOnValid (parseFunctionReturns nested) :=
  parseFunctionReturns_invariantFreeOnValid nested contract

example (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseFunctionType nested input ≠ .invariant error :=
  parseFunctionType_ne_invariant nested contract input inputValid error

end Solcore.Test.SyntaxParserTypeFunctionTotalityProperties
