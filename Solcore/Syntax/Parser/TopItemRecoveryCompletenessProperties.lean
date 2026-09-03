import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties
import Solcore.Syntax.Parser.TopItemRecoveryOrdinaryOutcomeSoundnessProperties

/-! Unconditional complete ordinary grammar correspondence for standalone
top-item recovery, including its mandatory-first-token rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Recovery grammar success is exactly execution with the same recovered
item AST and declarative remainder, without a valid-state premise. -/
theorem recoverTopItem_ordinary_success_iff
    {input : State} {value : TopItem}
    {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TopItemRecoveryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, recoverTopItem input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok recoverTopItem recoverTopItem_exactOutcomeSpec
    (recoverTopItem_ne_invariant input)
    recoverTopItem_success_ordinaryOutcome_sound recoverTopItem_reject_ordinaryOutcome_sound

/-- Recovery grammar rejection is exactly execution at the same declarative
endpoint, without identifying the failure payload or requiring valid input. -/
theorem recoverTopItem_ordinary_reject_iff
    {input : State} {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TopItemRecoveryRejects input.declarativeRemainder rejected ↔
      ∃ failure output, recoverTopItem input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject recoverTopItem recoverTopItem_exactOutcomeSpec
    (recoverTopItem_ne_invariant input)
    recoverTopItem_success_ordinaryOutcome_sound recoverTopItem_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser.FileInternals
