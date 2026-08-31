import Solcore.Syntax.Parser.TypeSimpleTotalityProperties

/-! External consumers for simple recursive type-form totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @parseMappingType_invariantFreeOnValid
example := @parseMappingType_ne_invariant
example := @parseComptimeType_invariantFreeOnValid
example := @parseComptimeType_ne_invariant
example := @parseProxyType_invariantFreeOnValid
example := @parseProxyType_ne_invariant
example := @parseTupleType_invariantFreeOnValid
example := @parseTupleType_ne_invariant

end Tests
