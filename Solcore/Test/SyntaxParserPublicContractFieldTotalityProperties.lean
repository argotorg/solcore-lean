import Solcore.Syntax.Parser.PublicContractFieldTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicContractFieldTotalityProperties

open Solcore.Syntax.Parser

example := @contractField_invariantFreeOnValid
example := @contractField_ne_invariant
example := @contractField_cursor_lt_onSuccess
example := @contractField_elementTotalityContract
example :=
  @ContractInternals.contractMemberTotalityContract_of_remainingBranches

end Solcore.Test.SyntaxParserPublicContractFieldTotalityProperties
