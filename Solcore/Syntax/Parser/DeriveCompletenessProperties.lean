import Solcore.Syntax.Parser.DeriveAttributeOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DeriveAttributeTotalityProperties
import Solcore.Syntax.Parser.DeriveTargetOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties

/-! Complete derive-target and normal, recovered, and public attribute outcomes.
Target and recovery correspondence needs no state-validity assumption. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Independent deriveTarget success corresponds exactly to execution with the
same AST and declarative remainder on every input. -/
theorem deriveTarget_ordinary_success_iff
    {input : State}
    {value : DeriveTarget} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveTargetParses
      input.declarativeRemainder value remainder ↔
      ∃ output, deriveTarget input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok deriveTarget deriveTarget_exactOutcomeSpec
    (deriveTarget_ne_invariant input)
    deriveTarget_success_ordinaryOutcome_sound deriveTarget_reject_ordinaryOutcome_sound

/-- Independent deriveTarget rejection corresponds exactly to execution at the
same declarative endpoint on every input, leaving diagnostics existential. -/
theorem deriveTarget_ordinary_reject_iff
    {input : State}
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveTargetRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, deriveTarget input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject deriveTarget deriveTarget_exactOutcomeSpec
    (deriveTarget_ne_invariant input)
    deriveTarget_success_ordinaryOutcome_sound deriveTarget_reject_ordinaryOutcome_sound

/-- Independent deriveAttributeValid success corresponds exactly to execution with the
same AST and declarative remainder on a valid input. -/
theorem deriveAttributeValid_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveAttributeParses
      input.declarativeRemainder value remainder ↔
      ∃ output, DeriveAttributeInternals.valid input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok DeriveAttributeInternals.valid deriveAttributeValid_exactOutcomeSpec
    (DeriveAttributeInternals.valid_ne_invariant input inputValid)
    deriveAttributeValid_success_ordinaryOutcome_sound deriveAttributeValid_reject_ordinaryOutcome_sound

/-- Independent deriveAttributeValid rejection corresponds exactly to execution at the
same declarative endpoint on a valid input, leaving diagnostics existential. -/
theorem deriveAttributeValid_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveAttributeValidRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, DeriveAttributeInternals.valid input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject DeriveAttributeInternals.valid deriveAttributeValid_exactOutcomeSpec
    (DeriveAttributeInternals.valid_ne_invariant input inputValid)
    deriveAttributeValid_success_ordinaryOutcome_sound deriveAttributeValid_reject_ordinaryOutcome_sound

/-- Independent deriveAttributeRecovered success corresponds exactly to execution with the
same AST and declarative remainder on every input. -/
theorem deriveAttributeRecovered_ordinary_success_iff
    {input : State}
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveAttributeRecoveredParses
      input.declarativeRemainder value remainder ↔
      ∃ output, DeriveAttributeInternals.recovered input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok DeriveAttributeInternals.recovered deriveAttributeRecovered_exactOutcomeSpec
    (DeriveAttributeInternals.recovered_ne_invariant input)
    deriveAttributeRecovered_success_ordinaryOutcome_sound deriveAttributeRecovered_reject_ordinaryOutcome_sound

/-- Independent deriveAttributeRecovered rejection corresponds exactly to execution at the
same declarative endpoint on every input, leaving diagnostics existential. -/
theorem deriveAttributeRecovered_ordinary_reject_iff
    {input : State}
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveAttributeRecoveredRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, DeriveAttributeInternals.recovered input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject DeriveAttributeInternals.recovered deriveAttributeRecovered_exactOutcomeSpec
    (DeriveAttributeInternals.recovered_ne_invariant input)
    deriveAttributeRecovered_success_ordinaryOutcome_sound deriveAttributeRecovered_reject_ordinaryOutcome_sound

/-- Independent deriveAttribute success corresponds exactly to execution with the
same AST and declarative remainder on a valid input. -/
theorem deriveAttribute_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : DeriveAttribute} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveAttributeOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, deriveAttribute input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok deriveAttribute deriveAttribute_exactOutcomeSpec
    (deriveAttribute_ne_invariant input inputValid)
    deriveAttribute_success_ordinaryOutcome_sound deriveAttribute_reject_ordinaryOutcome_sound

/-- Independent deriveAttribute rejection corresponds exactly to execution at the
same declarative endpoint on a valid input, leaving diagnostics existential. -/
theorem deriveAttribute_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.DeriveAttributeRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, deriveAttribute input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject deriveAttribute deriveAttribute_exactOutcomeSpec
    (deriveAttribute_ne_invariant input inputValid)
    deriveAttribute_success_ordinaryOutcome_sound deriveAttribute_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser
