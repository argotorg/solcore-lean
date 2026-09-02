import Solcore.Syntax.DeclarativeContractFieldExactnessProperties
import Solcore.Syntax.Parser.ContractFieldOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ContractFieldOrdinarySuccessSoundnessProperties

/-! Complete executable ordinary outcomes for contract storage fields. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractInternals

/-- Package executable contract-field success and exact rejection. -/
theorem contractField_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {field : ContractField},
      contractField expression input = .ok field output →
        DeclarativeGrammar.ContractFieldOrdinaryParses expressionOrdinary
          input.declarativeRemainder field output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      contractField expression input = .reject failure rejected →
        DeclarativeGrammar.ContractFieldRejects expressionOrdinary
          expressionRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨contractField_success_ordinaryOutcome_sound expression
      expressionOrdinary expressionSuccessSound,
    contractField_reject_ordinaryOutcome_sound expression expressionOrdinary
      expressionRejects expressionSuccessSound expressionRejectSound⟩

/-- Re-export deterministic contract-field outcomes with the fixed public Core
type outcome. -/
theorem contractField_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ContractFieldOrdinaryParses expressionOrdinary)
      (DeclarativeGrammar.ContractFieldRejects expressionOrdinary
        expressionRejects) :=
  DeclarativeGrammar.contractFieldDeterministicOutcomeSpec
    expressionOutcomes

/-- Re-export exact field outcomes from an exact initializer-expression
contract. -/
theorem contractField_exactOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.ContractFieldOrdinaryParses expressionOrdinary)
      (DeclarativeGrammar.ContractFieldRejects expressionOrdinary
        expressionRejects) :=
  DeclarativeGrammar.contractFieldExactOutcomeSpec expressionOutcomes

/-- Under an exact expression contract, two executable field successes have
the same AST and declarative remainder. -/
theorem contractField_success_result_unique
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      expressionOrdinary expressionRejects)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input leftOutput rightOutput : State}
    {left right : ContractField}
    (leftResult : contractField expression input = .ok left leftOutput)
    (rightResult : contractField expression input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (contractField_exactOutcomeSpec expressionOutcomes).successResultUnique
    (contractField_success_ordinaryOutcome_sound expression
      expressionOrdinary expressionSuccessSound leftResult)
    (contractField_success_ordinaryOutcome_sound expression
      expressionOrdinary expressionSuccessSound rightResult)

/-- Under an exact expression contract, two executable field rejections have
the same declarative endpoint. -/
theorem contractField_reject_output_unique
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      expressionOrdinary expressionRejects)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : contractField expression input =
      .reject leftFailure leftOutput)
    (rightResult : contractField expression input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (contractField_exactOutcomeSpec expressionOutcomes).rejectOutputUnique
    (contractField_reject_ordinaryOutcome_sound expression
      expressionOrdinary expressionRejects expressionSuccessSound
        expressionRejectSound leftResult)
    (contractField_reject_ordinaryOutcome_sound expression
      expressionOrdinary expressionRejects expressionSuccessSound
        expressionRejectSound rightResult)

end ContractInternals
end Solcore.Syntax.Parser
