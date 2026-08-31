import Solcore.Syntax.Parser.DeriveRecoveryTotalityProperties

/-! External consumers for derive recovery totality. -/

namespace Tests

open Solcore.Syntax.Parser

example :=
  @DeriveAttributeInternals.recoverTail_ordinary_of_remainingCount_lt
example :=
  @DeriveAttributeInternals.recoverTail_ne_invariant_of_remainingCount_lt
example := @DeriveAttributeInternals.recoverTail_production_ordinary
example := @DeriveAttributeInternals.recovered_ordinary
example := @DeriveAttributeInternals.recovered_ne_invariant

end Tests
