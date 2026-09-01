import Solcore.Syntax.Parser.CanonicalParserTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCanonicalParserTotalityProperties

open Solcore.Syntax.Parser

example := @FileInternals.productionPlainTopItemTotalityContract
example := @FileInternals.productionPlainTopItem_ordinary
example := @FileInternals.productionPlainTopItem_invariantFreeOnValid
example := @FileInternals.productionPlainTopItem_ne_invariant
example := @FileInternals.productionTopItem_ordinary
example := @FileInternals.productionTopItem_invariantFreeOnValid
example := @FileInternals.productionTopItem_ne_invariant
example := @FileInternals.productionParseItemsItem_ordinary
example := @FileInternals.productionParseItemsItem_invariantFreeOnValid
example := @FileInternals.productionParseItemsItem_ne_invariant
example := @FileInternals.productionParseItemsItemInvariantFree
example := @FileInternals.productionSourceFile_exists_ok
example := @FileInternals.productionSourceFile_ordinary
example := @FileInternals.productionSourceFile_invariantFreeOnValid
example := @FileInternals.productionSourceFile_ne_invariant
example := @productionParseLexed_exists_ok
example := @productionParseLexed_ne_error
example := @productionParse_exists_ok
example := @productionParse_ne_error

end Solcore.Test.SyntaxParserCanonicalParserTotalityProperties
