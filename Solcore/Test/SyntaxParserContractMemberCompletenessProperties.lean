import Solcore.Syntax.Parser.ContractMemberCompletenessProperties

/-! External consumers of both directions of contract-internal completeness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractMemberCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example {input : State} (inputValid : input.ValidFor)
    {value : ContractField} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ContractFieldOrdinaryParses
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, contractField expression input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (contractFieldPublic_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : ContractField} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : contractField expression input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.ContractFieldOrdinaryParses
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      input.declarativeRemainder value remainder :=
  (contractFieldPublic_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ContractFieldRejects
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      DeclarativeGrammar.CoreExpressionPublicRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, contractField expression input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (contractFieldPublic_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : contractField expression input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.ContractFieldRejects
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      DeclarativeGrammar.CoreExpressionPublicRejects
      input.declarativeRemainder rejected :=
  (contractFieldPublic_ordinary_reject_iff inputValid).mpr
    ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, contractMemberCore input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (contractMemberCore_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : contractMemberCore input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      input.declarativeRemainder value remainder :=
  (contractMemberCore_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ContractMemberCoreRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, contractMemberCore input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (contractMemberCore_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : contractMemberCore input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.ContractMemberCoreRejects
      input.declarativeRemainder rejected :=
  (contractMemberCore_ordinary_reject_iff inputValid).mpr
    ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ContractMemberOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, contractMemberWithAttribute input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (contractMemberWithAttribute_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : ContractMember} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : contractMemberWithAttribute input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.ContractMemberOrdinaryParses
      input.declarativeRemainder value remainder :=
  (contractMemberWithAttribute_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ContractMemberRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, contractMemberWithAttribute input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (contractMemberWithAttribute_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : contractMemberWithAttribute input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.ContractMemberRejects
      input.declarativeRemainder rejected :=
  (contractMemberWithAttribute_ordinary_reject_iff inputValid).mpr
    ⟨failure, output, result, remainderEq⟩

end Solcore.Test.SyntaxParserContractMemberCompletenessProperties
