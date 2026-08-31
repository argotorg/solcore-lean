import Solcore.Syntax.Parser.DelimitedTotalityProperties

/-! External consumers for generic delimited-loop totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @ElementTotalityContract
example := @afterDelimitedElement_ordinary_of_remainingCount_lt
example := @afterDelimitedElement_ne_invariant_of_remainingCount_lt
example := @delimitedWithPolicy_ordinary
example := @delimitedWithPolicy_ne_invariant
example := @delimited_ordinary
example := @delimited_ne_invariant
example := @delimitedNoTrailing_ordinary
example := @delimitedNoTrailing_ne_invariant

end Tests
