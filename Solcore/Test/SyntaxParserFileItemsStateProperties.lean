import Solcore.Syntax.Parser.FileItemsStateProperties

/-! External consumers for complete-file state-transition laws. -/

namespace Tests

open Solcore.Syntax.Parser

example := @FileInternals.parseItems_preservesTokenWindow
example := @FileInternals.parseItems_preservesTokensOnSuccess
example := @FileInternals.parseItems_cursorMonotoneOnSuccess
example := @FileInternals.sourceFile_preservesTokenWindow
example := @FileInternals.sourceFile_preservesTokensOnSuccess
example := @FileInternals.sourceFile_cursorMonotoneOnSuccess

end Tests
