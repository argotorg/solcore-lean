import Solcore.Syntax.Parser.TypeAliasTotalityProperties

/-! External consumers for complete type-alias totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @parseTypeAliasParameters_invariantFreeOnValid
example := @parseTypeAliasParameters_ne_invariant
example := @TypeAliasInternals.parseAliasValue_invariantFreeOnValid
example := @TypeAliasInternals.parseAliasValue_ne_invariant
example := @typeAlias_invariantFreeOnValid
example := @typeAlias_ne_invariant

end Tests
