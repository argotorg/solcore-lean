import Solcore.Syntax.Parser.ExportNameTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportNameTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @ExportInternals.exportName_invariantFreeOnValid
example := @ExportInternals.exportName_ordinary
example := @ExportInternals.exportName_ne_invariant
example := @ExportInternals.exportName_cursor_lt_onSuccess
example := @ExportInternals.exportName_elementTotalityContract

end Solcore.Test.SyntaxParserExportNameTotalityProperties
