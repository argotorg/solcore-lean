import Solcore.Syntax.Parser.ExportProperties

/-! External consumers for canonical export parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax.Parser

example := @exportPath_validFor
example := @exportPath_preservesTokenWindow
example := @exportPath_preservesTokensOnSuccess
example := @exportPath_cursorMonotoneOnSuccess
example := @exportPath_startsAtCurrentTokenOnSuccess
example := @constructorSelection_validFor
example := @constructorSelection_preservesTokenWindow
example := @constructorSelection_preservesTokensOnSuccess
example := @constructorSelection_cursorMonotoneOnSuccess
example := @constructorSelection_startsAtCurrentTokenOnSuccess
example := @exportName_validFor
example := @exportName_preservesTokenWindow
example := @exportName_preservesTokensOnSuccess
example := @exportName_cursorMonotoneOnSuccess
example := @exportName_startsAtCurrentTokenOnSuccess
example := @localExportItem_validFor
example := @localExportItem_preservesTokenWindow
example := @localExportItem_preservesTokensOnSuccess
example := @localExportItem_cursorMonotoneOnSuccess
example := @localExportItem_startsAtCurrentTokenOnSuccess
example := @exportSelection_validFor
example := @exportSelection_preservesTokenWindow
example := @exportSelection_preservesTokensOnSuccess
example := @exportSelection_cursorMonotoneOnSuccess
example := @exportSelection_startsAtCurrentTokenOnSuccess
example := @finishExport_validFor
example := @finishExport_preservesTokenWindow
example := @finishExport_preservesTokensOnSuccess
example := @finishExport_cursorMonotoneOnSuccess
example := @finishExport_keepsStartByte
example := @localExport_validFor
example := @localExport_preservesTokenWindow
example := @localExport_preservesTokensOnSuccess
example := @localExport_cursorMonotoneOnSuccess
example := @localExport_keepsStartByte
example := @pathExport_validFor
example := @pathExport_preservesTokenWindow
example := @pathExport_preservesTokensOnSuccess
example := @pathExport_cursorMonotoneOnSuccess
example := @pathExport_keepsStartByte
example := @exportDecl_validFor
example := @exportDecl_preservesTokenWindow
example := @exportDecl_preservesTokensOnSuccess
example := @exportDecl_cursorMonotoneOnSuccess
example := @exportDecl_startsAtCurrentTokenOnSuccess

end Tests
