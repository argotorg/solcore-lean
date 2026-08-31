import Solcore.Syntax.Parser.ContractProperties

set_option autoImplicit false

namespace Tests
open Solcore.Syntax.Parser

example := @ContractInternals.contractField_validFor
example := @ContractInternals.contractField_preservesTokenWindow
example := @ContractInternals.contractField_preservesTokensOnSuccess
example := @ContractInternals.contractField_cursorMonotoneOnSuccess
example := @ContractInternals.contractField_startsAtCurrentTokenOnSuccess
end Tests
