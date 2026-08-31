import Solcore.Syntax.Parser.PredicateProperties

/-! External compile consumers for canonical predicate contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := predicate_validFor
example := predicate_preservesTokenWindow
example := predicate_preservesTokensOnSuccess
example := predicate_cursorMonotoneOnSuccess
example := predicate_startsAtCurrentTokenOnSuccess

end Tests
