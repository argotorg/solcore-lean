import Solcore.Syntax.Parser.ExportProperties

/-! External consumers for canonical export-path shape contracts. -/

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

end Tests
