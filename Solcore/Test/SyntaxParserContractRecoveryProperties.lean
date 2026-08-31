import Solcore.Syntax.Parser.ContractRecoveryProperties

set_option autoImplicit false

namespace Tests
open Solcore.Syntax.Parser

example := @ContractInternals.RecoveredContractMemberValid
example := @ContractInternals.finishRecoveredMember_validFor
example := @ContractInternals.recoverContractMemberAux_validFor
example := @ContractInternals.recoverContractMember_validFor
example := @ContractInternals.finishRecoveredMember_preservesTokenWindow
example := @ContractInternals.recoverContractMemberAux_preservesTokenWindow
example := @ContractInternals.recoverContractMemberAux_preservesTokensOnSuccess
example := @ContractInternals.recoverContractMemberAux_ok_state_shape
example := @ContractInternals.recoverContractMemberAux_cursorMonotoneOnSuccess
example := @ContractInternals.recoverContractMember_preservesTokenWindow
example := @ContractInternals.recoverContractMember_preservesTokensOnSuccess
example := @ContractInternals.recoverContractMember_ok_state_shape
example := @ContractInternals.recoverContractMember_cursor_lt_onSuccess
example := @ContractInternals.recoverContractMember_cursorMonotoneOnSuccess
example := @ContractInternals.recoverContractMember_startsAtCurrentTokenOnSuccess

end Tests
