import Solcore.Syntax.Parser.FileRecoveryProperties

/-! External consumers for canonical top-level recovery contracts. -/

namespace Tests

open Solcore.Syntax.Parser

example := @FileInternals.finishRecoveredTopItem
example := @FileInternals.recoverTopItemAux
example := @FileInternals.recoverTopItem
example := @FileInternals.RecoveredTopItemValid
example := @FileInternals.finishRecoveredTopItem_validFor
example := @FileInternals.recoverTopItemAux_validFor
example := @FileInternals.recoverTopItem_validFor
example := @FileInternals.finishRecoveredTopItem_preservesTokenWindow
example := @FileInternals.recoverTopItemAux_preservesTokenWindow
example := @FileInternals.recoverTopItemAux_preservesTokensOnSuccess
example := @FileInternals.recoverTopItemAux_ok_state_shape
example := @FileInternals.recoverTopItemAux_cursorMonotoneOnSuccess
example := @FileInternals.recoverTopItem_preservesTokenWindow
example := @FileInternals.recoverTopItem_preservesTokensOnSuccess
example := @FileInternals.recoverTopItem_ok_state_shape
example := @FileInternals.recoverTopItem_cursor_lt_onSuccess
example := @FileInternals.recoverTopItem_cursorMonotoneOnSuccess
example := @FileInternals.recoverTopItem_startsAtCurrentTokenOnSuccess

end Tests
