import Solcore.Syntax.Parser.ContractBodyStateProperties

set_option autoImplicit false

namespace Tests
open Solcore.Syntax.Parser

example := @ContractInternals.closeContractBody_preservesTokenWindow
example := @ContractInternals.contractMembers_preservesTokenWindow
example := @ContractInternals.contractMembers_ok_state_shape
example := @ContractInternals.contractBody_preservesTokenWindow
example := @ContractInternals.contractBody_preservesTokensOnSuccess
example := @ContractInternals.contractBody_ok_state_shape
example := @ContractInternals.contractBody_cursor_lt_onSuccess
example := @ContractInternals.contractBody_cursorMonotoneOnSuccess
example := @ContractInternals.contractBody_startsAtCurrentTokenOnSuccess

end Tests
