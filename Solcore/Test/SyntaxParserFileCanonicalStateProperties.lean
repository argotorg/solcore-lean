import Solcore.Syntax.Parser.FileCanonicalStateProperties

/-! External consumers for canonical complete-file state laws. -/

namespace Tests

open Solcore.Syntax.Parser

example := @FileInternals.parseItems_canonical_preservesTokenWindow
example := @FileInternals.parseItems_canonical_preservesTokensOnSuccess
example := @FileInternals.parseItems_canonical_cursorMonotoneOnSuccess
example := @FileInternals.sourceFile_canonical_preservesTokenWindow
example := @FileInternals.sourceFile_canonical_preservesTokensOnSuccess
example := @FileInternals.sourceFile_canonical_cursorMonotoneOnSuccess

end Tests
