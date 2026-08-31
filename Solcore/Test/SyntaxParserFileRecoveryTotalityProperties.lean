import Solcore.Syntax.Parser.FileRecoveryTotalityProperties

/-! External consumers for top-level recovery totality contracts. -/

namespace Tests

open Solcore.Syntax.Parser

example :=
  @FileInternals.recoverTopItemAux_exists_ok_of_remainingCount_lt
example := @FileInternals.recoverTopItemAux_production_exists_ok
example := @FileInternals.recoverTopItem_ordinary
example := @FileInternals.recoverTopItem_ne_invariant
example := @FileInternals.recoverTopItem_exists_ok_of_validFor_not_atEnd
example := @FileInternals.recoverTopItem_eq_rejectAt_of_atEnd
example := @FileInternals.recoverTopItem_exists_ok_iff_not_atEnd

end Tests
