import Solcore.Syntax.Parser.DeriveAttributeOrdinaryOutcomeSoundnessProperties

/-! External consumers for derive-attribute grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeriveAttributeSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @DeriveAttributeParses
example := @DeriveAttributeValidRejects
example := @deriveAttributeValidDeterministicOutcomeSpec
example := @DeriveAttributeRecoveryDeclarationStartsAt
example := @DeriveAttributeRecoveryStops
example := @DeriveAttributeRecoveryTailParses
example := @DeriveAttributeRecoveredParses
example := @DeriveAttributeRecoveredRejects
example := @deriveAttributeRecoveredDeterministicOutcomeSpec
example := @DeriveAttributeOrdinaryParses
example := @DeriveAttributeRejects
example := @deriveAttributeDeterministicOutcomeSpec
example := @DeriveAttributeParses.value_unique
example := @DeriveAttributeParses.result_unique
example := @DeriveAttributeValidRejects.output_unique
example := @deriveAttributeValidExactOutcomeSpec
example := @DeriveAttributeRecoveryTailParses.value_unique
example := @DeriveAttributeRecoveryTailParses.result_unique
example := @DeriveAttributeRecoveredParses.value_unique
example := @DeriveAttributeRecoveredParses.result_unique
example := @DeriveAttributeRecoveredRejects.output_unique
example := @deriveAttributeRecoveredExactOutcomeSpec
example := @DeriveAttributeOrdinaryParses.value_unique
example := @DeriveAttributeOrdinaryParses.result_unique
example := @DeriveAttributeRejects.output_unique
example := @deriveAttributeExactOutcomeSpec
example := @deriveAttributeValid_success_sound
example := @DeriveAttributeInternals.valid_reject_ordinaryOutcome_sound
example := @deriveAttributeValid_success_ordinaryOutcome_sound
example := @deriveAttributeValid_reject_ordinaryOutcome_sound
example := @deriveAttributeValid_ordinaryOutcome_sound
example := @deriveAttributeValid_ordinaryOutcomeSpec
example := @deriveAttributeValid_exactOutcomeSpec
example := @deriveAttributeValid_success_result_unique
example := @deriveAttributeValid_reject_output_unique
example :=
  @DeriveAttributeInternals.recoveryDeclarationStartsAt_of_atDeriveDeclarationBoundary_eq_true
example :=
  @DeriveAttributeInternals.atDeriveDeclarationBoundary_eq_true_of_recoveryDeclarationStartsAt
example := @DeriveAttributeInternals.recoveryStops_of_unclosedGuard_eq_true
example := @DeriveAttributeInternals.recoveryStops_of_advance?_eq_none
example := @DeriveAttributeInternals.no_recoveryStops_of_nonBoundary_token
example := @DeriveAttributeInternals.recoverTail_success_ordinaryOutcome_sound
example :=
  @DeriveAttributeInternals.recoverTail_production_success_ordinaryOutcome_sound
example := @deriveAttributeRecovered_success_ordinaryOutcome_sound
example := @deriveAttributeRecovered_reject_ordinaryOutcome_sound
example := @deriveAttributeRecovered_ordinaryOutcome_sound
example := @deriveAttributeRecovered_ordinaryOutcomeSpec
example := @deriveAttributeRecovered_exactOutcomeSpec
example := @deriveAttributeRecovered_success_result_unique
example := @deriveAttributeRecovered_reject_output_unique
example := @deriveAttribute_success_ordinaryOutcome_sound
example := @deriveAttribute_reject_ordinaryOutcome_sound
example := @deriveAttribute_ordinaryOutcome_sound
example := @deriveAttribute_ordinaryOutcomeSpec
example := @deriveAttribute_exactOutcomeSpec
example := @deriveAttribute_success_result_unique
example := @deriveAttribute_reject_output_unique
example := @deriveAttribute_success_sound
example := @deriveAttribute_success_sound_and_validFor

example {input next : State} {value : DeriveAttribute}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : deriveAttribute input = .ok value next) :
    DeriveAttributeParses input.declarativeRemainder value
      next.declarativeRemainder :=
  deriveAttribute_success_sound diagnosticFree result

example {input next : State} {value : DeriveAttribute}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (result : deriveAttribute input = .ok value next) :
    DeriveAttributeParses input.declarativeRemainder value
        next.declarativeRemainder ∧
      value.ValidFor input.file :=
  deriveAttribute_success_sound_and_validFor inputValid diagnosticFree result

example {input rejected : State} {failure : Failure}
    (result : DeriveAttributeInternals.valid input =
      .reject failure rejected) :
    DeriveAttributeValidRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  deriveAttributeValid_reject_ordinaryOutcome_sound result

example {input next : State} {value : DeriveAttribute}
    (result : DeriveAttributeInternals.recovered input = .ok value next) :
    DeriveAttributeRecoveredParses input.declarativeRemainder value
      next.declarativeRemainder :=
  deriveAttributeRecovered_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : DeriveAttributeInternals.recovered input =
      .reject failure rejected) :
    DeriveAttributeRecoveredRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  deriveAttributeRecovered_reject_ordinaryOutcome_sound result

example {input next : State} {value : DeriveAttribute}
    (result : deriveAttribute input = .ok value next) :
    DeriveAttributeOrdinaryParses input.declarativeRemainder value
      next.declarativeRemainder :=
  deriveAttribute_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : deriveAttribute input = .reject failure rejected) :
    DeriveAttributeRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  deriveAttribute_reject_ordinaryOutcome_sound result

end Solcore.Test.SyntaxParserDeriveAttributeSoundnessProperties
