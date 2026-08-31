import Solcore.Syntax.Parser.PrimitiveTotalityProperties

/-! External consumers for primitive parser totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @Parser.Ordinary
example := @Parser.Ordinary.ne_invariant
example := @acceptToken_ordinary
example := @acceptToken_ne_invariant
example := @keyword_ordinary
example := @keyword_ne_invariant
example := @symbol_ordinary
example := @symbol_ne_invariant
example := @contextual_ordinary
example := @contextual_ne_invariant
example := @rawIdentifier_ordinary
example := @rawIdentifier_ne_invariant
example := @identifier_ordinary
example := @identifier_ne_invariant
example := @acceptToken_elementTotalityContract
example := @keyword_elementTotalityContract
example := @symbol_elementTotalityContract
example := @contextual_elementTotalityContract
example := @identifier_elementTotalityContract

end Tests
