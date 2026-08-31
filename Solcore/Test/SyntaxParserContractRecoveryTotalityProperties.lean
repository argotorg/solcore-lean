import Solcore.Syntax.Parser.ContractRecoveryTotalityProperties

/-! External consumers for contract-member recovery totality laws. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractRecoveryTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example := @recoverContractMemberAux_ok_of_remainingCount_lt
example := @recoverContractMemberAux_production_ok
example := @recoverContractMember_total
example := @recoverContractMember_ne_invariant
example := @recoverContractMember_reject_of_atEnd
example := @recoverContractMember_ok_of_valid_not_atEnd

example (state : State) (error : ParserInvariantError) :
    recoverContractMember state ≠ .invariant error :=
  recoverContractMember_ne_invariant state error

example (state : State) (atEnd : state.atEnd = true) :
    ∃ failure, recoverContractMember state = .reject failure state :=
  recoverContractMember_reject_of_atEnd state atEnd

example (state : State) (valid : state.ValidFor)
    (notEnd : state.atEnd = false) :
    ∃ member final, recoverContractMember state = .ok member final :=
  recoverContractMember_ok_of_valid_not_atEnd state valid notEnd

end Solcore.Test.SyntaxParserContractRecoveryTotalityProperties
