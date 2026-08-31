import Solcore.Syntax.Parser.ExportSelectionItemTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportSelectionItemTotalityProperties

open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExportInternals

example (nameContract : ElementTotalityContract exportName) :
    ElementTotalityContract localExportItem :=
  localExportItem_elementTotalityContract nameContract

example (nameContract : ElementTotalityContract exportName) :
    ExportLeafTotalityContract :=
  exportLeafTotalityContract nameContract

end Solcore.Test.SyntaxParserExportSelectionItemTotalityProperties
