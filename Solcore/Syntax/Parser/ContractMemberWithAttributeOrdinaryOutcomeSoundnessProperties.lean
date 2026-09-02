import Solcore.Syntax.DeclarativeContractMemberWithAttributeExactnessProperties
import Solcore.Syntax.Parser.ContractMemberWithAttributeOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ContractMemberWithAttributeOrdinarySuccessSoundnessProperties

/-! Complete broad executable outcomes for derive-aware contract members. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Package unconditional executable success and exact selected-stage
rejection for derive-aware contract members. -/
theorem contractMemberWithAttribute_ordinaryOutcome_sound :
    (∀ {input output : State} {member : ContractMember},
      contractMemberWithAttribute input = .ok member output →
        DeclarativeGrammar.ContractMemberOrdinaryParses
          input.declarativeRemainder member output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      contractMemberWithAttribute input = .reject failure rejected →
        DeclarativeGrammar.ContractMemberRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨contractMemberWithAttribute_success_ordinaryOutcome_sound,
    contractMemberWithAttribute_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive derive-aware member outcomes. -/
theorem contractMemberWithAttribute_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberOrdinaryParses
      DeclarativeGrammar.ContractMemberRejects :=
  DeclarativeGrammar.contractMemberDeterministicOutcomeSpec

/-- Re-export exact derive-aware member outcomes conditional only on an exact
attribute-free core contract. -/
theorem contractMemberWithAttribute_exactOutcomeSpec_of_core
    (coreOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberOrdinaryParses
      DeclarativeGrammar.ContractMemberRejects :=
  DeclarativeGrammar.contractMemberExactOutcomeSpecOfCore coreOutcomes

/-- Under an exact core contract, two successful executable reflections have
the same member AST and final declarative remainder. -/
theorem contractMemberWithAttribute_success_result_unique_of_core
    (coreOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects)
    {input leftOutput rightOutput : State}
    {left right : ContractMember}
    (leftResult : contractMemberWithAttribute input = .ok left leftOutput)
    (rightResult : contractMemberWithAttribute input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ContractMemberOrdinaryParses.result_unique_of_core
    coreOutcomes
    (contractMemberWithAttribute_success_ordinaryOutcome_sound leftResult)
    (contractMemberWithAttribute_success_ordinaryOutcome_sound rightResult)

/-- Under an exact core contract, two rejected executable reflections have
the same exact declarative endpoint. -/
theorem contractMemberWithAttribute_reject_output_unique_of_core
    (coreOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : contractMemberWithAttribute input =
      .reject leftFailure leftOutput)
    (rightResult : contractMemberWithAttribute input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ContractMemberRejects.output_unique_of_core coreOutcomes
    (contractMemberWithAttribute_reject_ordinaryOutcome_sound leftResult)
    (contractMemberWithAttribute_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.ContractInternals
