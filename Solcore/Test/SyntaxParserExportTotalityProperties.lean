import Solcore.Syntax.Parser.ExportTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example (contract : ExportLeafTotalityContract) :
    Parser.InvariantFreeOnValid exportDecl :=
  exportDecl_invariantFreeOnValid_of_leafContract contract

example (contract : ExportLeafTotalityContract)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    exportDecl input ≠ .invariant error :=
  exportDecl_ne_invariant_of_leafContract contract input inputValid error

end Solcore.Test.SyntaxParserExportTotalityProperties
