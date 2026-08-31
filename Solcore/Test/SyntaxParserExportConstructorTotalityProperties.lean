import Solcore.Syntax.Parser.ExportConstructorTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportConstructorTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExportInternals

example : Parser.InvariantFreeOnValid constructorSelection :=
  constructorSelection_invariantFreeOnValid

example (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    constructorSelection input ≠ .invariant error :=
  constructorSelection_ne_invariant input inputValid error

end Solcore.Test.SyntaxParserExportConstructorTotalityProperties
