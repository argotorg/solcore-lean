import Solcore.Syntax.Parser.ContractDeclarationTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractDeclarationTotalityProperties

open Solcore.Syntax.Parser

example := @ContractInternals.productionContractMemberTotalityContract
example := @ContractInternals.productionContractMemberCore_invariantFreeOnValid
example :=
  @ContractInternals.productionContractMemberWithAttribute_invariantFreeOnValid
example := @ContractInternals.productionContractMemberInvariantFreeOnValid
example := @ContractInternals.productionContractBody_ordinary
example := @ContractInternals.contractBody_invariantFreeOnValid
example := @contractDecl_invariantFreeOnValid
example := @contractDecl_ordinary
example := @contractDecl_ne_invariant

end Solcore.Test.SyntaxParserContractDeclarationTotalityProperties
