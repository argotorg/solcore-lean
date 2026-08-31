import Solcore.Syntax.Parser.FileItemsProperties

/-! External consumers for complete-file item validity. -/

namespace Tests

open Solcore.Syntax.Parser

example := @FileInternals.parseItemsItem
example := @FileInternals.parseItems_validFor
example := @FileInternals.sourceFile_reply_validFor

end Tests
