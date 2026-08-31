import Solcore.Syntax.Parser.ContractBodyTotalityProperties

/-! External consumers for conditional contract-body totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractBodyTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example := @ContractMemberInvariantFreeOnValid
example := @contractMembers_ordinary_of_remainingCount_lt
example := @contractMembers_production_ordinary
example := @contractBody_ordinary
example := @contractBody_ne_invariant

example (ordinary : ContractMemberInvariantFreeOnValid)
    (input : State) (valid : input.ValidFor)
    (error : ParserInvariantError) :
    contractBody input ≠ .invariant error :=
  contractBody_ne_invariant ordinary input valid error

end Solcore.Test.SyntaxParserContractBodyTotalityProperties
