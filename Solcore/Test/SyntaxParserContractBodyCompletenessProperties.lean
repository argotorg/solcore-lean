import Solcore.Syntax.Parser.ContractBodyCompletenessProperties

/-! Contract-body completeness consumers keep independent grammar spans and
forward member lists distinct from the executable body structure. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractBodyCompletenessProperties

open Solcore
open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example {input : State} (inputValid : input.ValidFor)
    {span : SourceSpan} {members : List ContractMember}
    {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ContractBodyOrdinaryParses
      input.declarativeRemainder span members remainder) :
    ∃ output, contractBody input = .ok ⟨span, members⟩ output ∧
      output.declarativeRemainder = remainder :=
  (contractBody_ordinary_success_iff inputValid
    (body := ⟨span, members⟩)).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {body : ContractBody} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : contractBody input = .ok body output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.ContractBodyOrdinaryParses
      input.declarativeRemainder body.span body.members remainder :=
  (contractBody_ordinary_success_iff inputValid).mpr
    ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ContractBodyRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, contractBody input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (contractBody_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : contractBody input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.ContractBodyRejects
      input.declarativeRemainder rejected :=
  (contractBody_ordinary_reject_iff inputValid).mpr
    ⟨failure, output, result, remainderEq⟩

end Solcore.Test.SyntaxParserContractBodyCompletenessProperties
