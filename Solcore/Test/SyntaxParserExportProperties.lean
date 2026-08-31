import Solcore.Syntax.Parser.ExportProperties

/-! External consumers for canonical export-path shape contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax.Parser

example := @exportPath_preservesTokenWindow
example := @exportPath_preservesTokensOnSuccess
example := @exportPath_cursorMonotoneOnSuccess
example := @exportPath_startsAtCurrentTokenOnSuccess

end Tests
