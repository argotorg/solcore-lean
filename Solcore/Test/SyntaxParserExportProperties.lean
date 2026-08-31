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

end Tests
