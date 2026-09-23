import Solcore.Syntax.Parser.ContractCanonicalProperties
import Solcore.Syntax.Parser.ContractEntry
import Solcore.Syntax.Parser.FunctionDeclarationTotalityProperties
import Solcore.Syntax.Parser.PublicContractFieldTotalityProperties

/-! Unconditional totality from contract members through contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractInternals

/-- All five production contract-member branches are invariant-free. -/
theorem productionContractMemberTotalityContract :
    ContractMemberTotalityContract :=
  contractMemberTotalityContract_of_remainingBranches
    (functionDecl_invariantFreeOnValid .contract)
    constructorDecl_invariantFreeOnValid
    fallbackDecl_invariantFreeOnValid

/-- Plain production member dispatch has only ordinary outcomes. -/
theorem productionContractMemberCore_invariantFreeOnValid :
    Parser.InvariantFreeOnValid contractMemberCore :=
  contractMemberCore_invariantFreeOnValid
    productionContractMemberTotalityContract

/-- Derive-aware production member dispatch has only ordinary outcomes. -/
theorem productionContractMemberWithAttribute_invariantFreeOnValid :
    Parser.InvariantFreeOnValid contractMemberWithAttribute :=
  contractMemberWithAttribute_invariantFreeOnValid
    productionContractMemberTotalityContract

theorem productionContractMemberWithAttribute_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractMemberWithAttribute input ≠ .invariant error :=
  productionContractMemberWithAttribute_invariantFreeOnValid.ne_invariant
    input inputValid error

/-- The concrete member contract discharges the contract-body loop premise. -/
theorem productionContractMemberInvariantFreeOnValid :
    ContractMemberInvariantFreeOnValid :=
  contractMemberInvariantFree_of_totalityContract
    productionContractMemberTotalityContract

/-- Production contract bodies have only ordinary outcomes on valid input. -/
theorem productionContractBody_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ body final, contractBody input = .ok body final) ∨
      (∃ failure final, contractBody input = .reject failure final) :=
  contractBody_ordinary productionContractMemberInvariantFreeOnValid
    input inputValid

theorem contractBody_invariantFreeOnValid :
    Parser.InvariantFreeOnValid contractBody :=
  productionContractBody_ordinary

theorem productionContractBody_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractBody input ≠ .invariant error :=
  contractBody_invariantFreeOnValid.ne_invariant input inputValid error

end ContractInternals

/-- Every production stage of a contract declaration is invariant-free. -/
theorem contractDecl_invariantFreeOnValid :
    Parser.InvariantFreeOnValid contractDecl := by
  unfold contractDecl
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .contractKw .topItem)
    (keyword_ordinary .contractKw .topItem).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    (identifier_validFor .topItem)
    (identifier_ordinary .topItem).invariantFreeOnValid
  intro name
  apply Parser.bind_invariantFreeOnValid
    optionalGenericParameters_validFor
    optionalGenericParameters_invariantFreeOnValid
  intro genericParameters
  apply Parser.bind_invariantFreeOnValid
    ContractInternals.contractBody_validFor
    ContractInternals.contractBody_invariantFreeOnValid
  intro body
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span body.span
    value := {
      name
      genericParameters
      bodySpan := body.span
      members := body.members
    }
  } : ContractDecl)

theorem contractDecl_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ declaration next, contractDecl input = .ok declaration next) ∨
      (∃ failure next, contractDecl input = .reject failure next) :=
  contractDecl_invariantFreeOnValid input inputValid

theorem contractDecl_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractDecl input ≠ .invariant error :=
  contractDecl_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
