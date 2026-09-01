import Solcore.Syntax.Parser.PredicateTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPredicateTotalityProperties

open Solcore.Syntax.Parser

example := @predicate_invariantFreeOnValid
example := @predicate_ne_invariant
example := @predicate_elementTotalityContract

end Solcore.Test.SyntaxParserPredicateTotalityProperties
