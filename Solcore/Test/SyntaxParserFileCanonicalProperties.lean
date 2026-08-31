import Solcore.Syntax.Parser.FileCanonicalProperties

namespace Tests
open Solcore.Syntax.Parser
example := @FileInternals.sourceFile_canonical_reply_validFor
example := @parseLexed_ok_canonical_validFor
example := @parse_ok_canonical_validFor
end Tests
