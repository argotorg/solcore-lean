import Solcore.Syntax.Parser.ContractDeclarationTotalityProperties
import Solcore.Syntax.Parser.CoreContractDeclarationExactnessProperties
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties

/-! Complete contract-body correspondence, preserving the grammar's covered
span and forward member list in the executable body structure. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

private theorem contractBody_parserValue_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (fun input (body : ContractBody) output =>
        DeclarativeGrammar.ContractBodyOrdinaryParses
          input body.span body.members output)
      DeclarativeGrammar.ContractBodyRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact contractBody_exactOutcomeSpec.successOutputUnique
      (show DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
        input (left.span, left.members) afterLeft from leftParsed)
      (show DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
        input (right.span, right.members) afterRight from rightParsed)
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨body, output, parsed⟩
    exact contractBody_exactOutcomeSpec.successRejectDisjoint rejection
      ⟨(body.span, body.members), output, parsed⟩
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    have bodyEq := contractBody_exactOutcomeSpec.successValueUnique
      (show DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
        input (left.span, left.members) afterLeft from leftParsed)
      (show DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
        input (right.span, right.members) afterRight from rightParsed)
    cases left
    cases right
    simp_all
  rejectOutputUnique := contractBody_exactOutcomeSpec.rejectOutputUnique

/-- Independent body success corresponds exactly to execution with the same
covered span, source-order members, and declarative remainder. -/
theorem contractBody_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {body : ContractBody} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractBodyOrdinaryParses
      input.declarativeRemainder body.span body.members remainder ↔
      ∃ output, contractBody input = .ok body output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok contractBody
    contractBody_parserValue_exactOutcomeSpec
    (productionContractBody_ne_invariant input inputValid)
    contractBody_success_ordinaryOutcome_sound
    contractBody_reject_ordinaryOutcome_sound

/-- Independent body rejection corresponds exactly to execution at the same
declarative endpoint, without identifying diagnostics or complete states. -/
theorem contractBody_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ContractBodyRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, contractBody input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject contractBody
    contractBody_parserValue_exactOutcomeSpec
    (productionContractBody_ne_invariant input inputValid)
    contractBody_success_ordinaryOutcome_sound
    contractBody_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser.ContractInternals
