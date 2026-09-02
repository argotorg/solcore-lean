import Solcore.Syntax.DeclarativeDeriveAttributeExactnessProperties
import Solcore.Syntax.Parser.DeriveAttributeRecoveredOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DeriveAttributeValidOrdinaryOutcomeSoundnessProperties

/-! Complete broad executable outcomes for public derive attributes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every public derive-attribute success is the preferred normal success or
the exact recovered success selected after a normal-path rejection. -/
theorem deriveAttribute_success_ordinaryOutcome_sound
    {input output : State} {value : DeriveAttribute}
    (result : deriveAttribute input = .ok value output) :
    DeclarativeGrammar.DeriveAttributeOrdinaryParses
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold deriveAttribute orElse at result
  cases validResult : DeriveAttributeInternals.valid input with
  | invariant error => simp [validResult] at result
  | ok normal afterNormal =>
      simp only [validResult] at result
      cases result
      exact .normal
        (deriveAttributeValid_success_ordinaryOutcome_sound validResult)
  | reject validFailure validRejected =>
      simp only [validResult] at result
      exact .recovered
        (deriveAttributeValid_reject_ordinaryOutcome_sound validResult)
        (deriveAttributeRecovered_success_ordinaryOutcome_sound result)

/-- Every public derive-attribute rejection records rejection of both the
normal attempt and recovery retried at the original input. -/
theorem deriveAttribute_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : deriveAttribute input = .reject failure rejected) :
    DeclarativeGrammar.DeriveAttributeRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold deriveAttribute orElse at result
  cases validResult : DeriveAttributeInternals.valid input with
  | invariant error => simp [validResult] at result
  | ok normal afterNormal => simp [validResult] at result
  | reject validFailure validRejected =>
      simp only [validResult] at result
      exact .both
        (deriveAttributeValid_reject_ordinaryOutcome_sound validResult)
        (deriveAttributeRecovered_reject_ordinaryOutcome_sound result)

/-- Package unconditional public success and exact double-rejection
reflection. -/
theorem deriveAttribute_ordinaryOutcome_sound :
    (∀ {input output : State} {value : DeriveAttribute},
      deriveAttribute input = .ok value output →
        DeclarativeGrammar.DeriveAttributeOrdinaryParses
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      deriveAttribute input = .reject failure rejected →
        DeclarativeGrammar.DeriveAttributeRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨deriveAttribute_success_ordinaryOutcome_sound,
    deriveAttribute_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive public derive-attribute outcomes. -/
theorem deriveAttribute_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.DeriveAttributeOrdinaryParses
      DeclarativeGrammar.DeriveAttributeRejects :=
  DeclarativeGrammar.deriveAttributeDeterministicOutcomeSpec

/-- Re-export full value and rejection-endpoint functionality for public
derive attributes at the executable reflection boundary. -/
theorem deriveAttribute_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.DeriveAttributeOrdinaryParses
      DeclarativeGrammar.DeriveAttributeRejects :=
  DeclarativeGrammar.deriveAttributeExactOutcomeSpec

/-- Two successful executable reflections have the same public derive
attribute and final declarative remainder. -/
theorem deriveAttribute_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : DeriveAttribute}
    (leftResult : deriveAttribute input = .ok left leftOutput)
    (rightResult : deriveAttribute input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveAttributeOrdinaryParses.result_unique
    (deriveAttribute_success_ordinaryOutcome_sound leftResult)
    (deriveAttribute_success_ordinaryOutcome_sound rightResult)

/-- Two rejected executable reflections have the same exact public
declarative endpoint. -/
theorem deriveAttribute_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : deriveAttribute input = .reject leftFailure leftOutput)
    (rightResult : deriveAttribute input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveAttributeRejects.output_unique
    (deriveAttribute_reject_ordinaryOutcome_sound leftResult)
    (deriveAttribute_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
