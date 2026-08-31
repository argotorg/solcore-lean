import Solcore.Syntax.Parser.ContractMemberTotalityProperties

/-! External consumers for conditional contract-member totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractMemberTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example := @mapMember_invariantFreeOnValid
example := @ContractMemberTotalityContract
example := @contractMemberParser_invariantFreeOnValid
example := @contractMemberCore_invariantFreeOnValid
example := @attachContractDerive_invariantFreeOnValid
example := @contractMemberWithAttribute_invariantFreeOnValid
example := @contractMemberWithAttribute_ne_invariant
example := @contractMemberInvariantFree_of_totalityContract
example := @contractBody_ordinary_of_memberTotalityContract
example := @contractBody_ne_invariant_of_memberTotalityContract

example (contract : ContractMemberTotalityContract) :
    ContractMemberInvariantFreeOnValid :=
  contractMemberInvariantFree_of_totalityContract contract

end Solcore.Test.SyntaxParserContractMemberTotalityProperties
