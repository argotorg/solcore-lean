import Solcore.Syntax.Parser.PublicCoreTermTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicCoreTermTotalityProperties

open Solcore.Syntax.Parser

example := @expression_invariantFreeOnValid
example := @expression_ne_invariant
example := @expression_elementTotalityContract
example := @pattern_invariantFreeOnValid
example := @pattern_ne_invariant
example := @pattern_elementTotalityContract
example := @block_invariantFreeOnValid
example := @block_ne_invariant
example := @block_elementTotalityContract

end Solcore.Test.SyntaxParserPublicCoreTermTotalityProperties
