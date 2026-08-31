import Solcore.Syntax.Parser.ParameterRecoveryTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserParameterRecoveryTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FunctionParameterInternals

example : Parser.Ordinary recoverParameter := recoverParameter_ordinary

example (state : State) (error : ParserInvariantError) :
    recoverParameter state ≠ .invariant error :=
  recoverParameter_ne_invariant state error

end Solcore.Test.SyntaxParserParameterRecoveryTotalityProperties
