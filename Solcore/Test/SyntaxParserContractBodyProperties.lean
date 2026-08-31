import Solcore.Syntax.Parser.ContractBodyProperties

set_option autoImplicit false

namespace Tests
open Solcore.Syntax.Parser

example := @ContractInternals.ContractBody
example := @ContractInternals.ContractBody.ValidFor
example := @ContractInternals.closeContractBody_validFor
example := @ContractInternals.contractMembers_validFor
example := @ContractInternals.contractBody_validFor

end Tests
