import Solcore.Syntax.Parser.ContractMemberRecoveryCompletenessProperties

/-! External consumers of both directions of contract-internal completeness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractMemberRecoveryCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example {input : State}
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ContractMemberRecoveryParses
      input.declarativeRemainder value remainder) :
    ∃ output, recoverContractMember input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (recoverContractMember_ordinary_success_iff).mp parsed

example {input : State}
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : recoverContractMember input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.ContractMemberRecoveryParses
      input.declarativeRemainder value remainder :=
  (recoverContractMember_ordinary_success_iff).mpr ⟨output, result, remainderEq⟩

example {input : State}
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ContractMemberRecoveryRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, recoverContractMember input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (recoverContractMember_ordinary_reject_iff).mp rejection

example {input : State}
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : recoverContractMember input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.ContractMemberRecoveryRejects
      input.declarativeRemainder rejected :=
  (recoverContractMember_ordinary_reject_iff).mpr
    ⟨failure, output, result, remainderEq⟩

end Solcore.Test.SyntaxParserContractMemberRecoveryCompletenessProperties
