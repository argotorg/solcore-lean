import Solcore.Syntax.Parser.BlockTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserBlockTotalityProperties

open Solcore.Syntax.Parser

example := @coreBlockItems_ne_invariant_of_remainingCount_lt

example := @coreBlock_invariantFreeOnValid

example := @BlockInternals.isolateBlock_invariantFreeOnValid

example := @BlockInternals.isolateBlock_cursor_lt_onSuccess

example := @isolatedCoreBlock_elementTotalityContract

end Solcore.Test.SyntaxParserBlockTotalityProperties
