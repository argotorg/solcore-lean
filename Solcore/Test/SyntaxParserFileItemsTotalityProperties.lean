import Solcore.Syntax.Parser.FileItemsTotalityProperties

/-! External consumers for conditional complete-file totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @FileInternals.ParseItemsItemInvariantFree
example := @FileInternals.parseItems_exists_ok_of_remainingCount_lt
example := @FileInternals.parseItems_production_exists_ok
example := @FileInternals.sourceFile_exists_ok

end Tests
