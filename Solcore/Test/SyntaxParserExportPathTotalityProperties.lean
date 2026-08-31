import Solcore.Syntax.Parser.ExportPathTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportPathTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExportInternals

example : Parser.Ordinary exportPath := exportPath_ordinary

example (input : State) (inputValid : input.ValidFor) :
    (∃ path next, exportPath input = .ok path next) ∨
    (∃ failure next, exportPath input = .reject failure next) :=
  exportPath_invariantFreeOnValid input inputValid

end Solcore.Test.SyntaxParserExportPathTotalityProperties
