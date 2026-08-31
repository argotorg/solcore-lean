import Solcore.Syntax.Parser.FileCompleteProperties

set_option autoImplicit false

namespace Tests
open Solcore.Syntax.Parser

example := @FileInternals.contractDecl_canonical_inputs
example := @FileInternals.parseItemsItem_complete_contract
example := @FileInternals.parseItemsItem_complete_validFor
example := @FileInternals.sourceFile_complete_reply_validFor
example := @FileInternals.parseItems_complete_preservesTokenWindow
example := @FileInternals.parseItems_complete_preservesTokensOnSuccess
example := @FileInternals.parseItems_complete_cursorMonotoneOnSuccess
example := @FileInternals.sourceFile_complete_preservesTokenWindow
example := @FileInternals.sourceFile_complete_preservesTokensOnSuccess
example := @FileInternals.sourceFile_complete_cursorMonotoneOnSuccess
example := @parseLexed_ok_complete_validFor
example := @parse_ok_complete_validFor

end Tests
