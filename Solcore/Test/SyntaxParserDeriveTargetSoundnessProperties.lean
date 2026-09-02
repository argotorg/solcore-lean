import Solcore.Syntax.Parser.DeriveTargetOrdinaryOutcomeSoundnessProperties

/-! External consumers for derive-target grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeriveTargetSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @ReservedDeriveTargetKeyword
example := @DeriveComponentParses
example := @DeriveTargetTailParses
example := @DeriveTargetParses
example := @ExactDeterministicOutcomeSpec
example := @ExactDeterministicOutcomeSpec.successResultUnique
example := @TokenAt.token_unique
example := @ExactTokenParses.result_unique
example := @IdentifierParses.result_unique
example := @IdentifierRejects.output_unique
example := @identifierExactOutcomeSpec
example := @DeriveReservedComponentAbsentAt
example := @DeriveComponentRejects
example := @deriveComponentDeterministicOutcomeSpec
example := @DeriveComponentParses.result_unique
example := @DeriveComponentRejects.output_unique
example := @deriveComponentExactOutcomeSpec
example := @DeriveTargetTailRejects
example := @deriveTargetTailDeterministicOutcomeSpec
example := @DeriveTargetTailParses.result_unique
example := @DeriveTargetTailRejects.output_unique
example := @deriveTargetTailExactOutcomeSpec
example := @DeriveTargetRejects
example := @deriveTargetDeterministicOutcomeSpec
example := @DeriveTargetParses.result_unique
example := @DeriveTargetRejects.output_unique
example := @deriveTargetExactOutcomeSpec
example := @deriveComponent_success_sound
example := @deriveComponent_reject_ordinaryOutcome_sound
example :=
  @DeriveTargetInternals.deriveTargetTail_production_reject_ordinaryOutcome_sound
example := @deriveTarget_success_sound
example := @deriveTarget_success_sound_and_validFor
example := @deriveTarget_success_ordinaryOutcome_sound
example := @deriveTarget_reject_ordinaryOutcome_sound
example := @deriveTarget_ordinaryOutcome_sound
example := @deriveTarget_ordinaryOutcomeSpec
example := @deriveTarget_exactOutcomeSpec
example := @deriveTarget_success_result_unique
example := @deriveTarget_reject_output_unique

example {input next : State} {target : DeriveTarget}
    (result : deriveTarget input = .ok target next) :
    DeriveTargetParses input.declarativeRemainder target
      next.declarativeRemainder :=
  deriveTarget_success_sound result

example {input next : State} {target : DeriveTarget}
    (inputValid : input.ValidFor)
    (result : deriveTarget input = .ok target next) :
    DeriveTargetParses input.declarativeRemainder target
        next.declarativeRemainder ∧
      target.ValidFor input.file :=
  deriveTarget_success_sound_and_validFor inputValid result

example {input rejected : State} {failure : Failure}
    (result : deriveTarget input = .reject failure rejected) :
    DeriveTargetRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  deriveTarget_reject_ordinaryOutcome_sound result

end Solcore.Test.SyntaxParserDeriveTargetSoundnessProperties
