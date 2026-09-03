import Solcore.Syntax.Parser.BlockTotalityProperties
import Solcore.Syntax.Parser.CoreBlockPublicExactnessProperties
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties
import Solcore.Syntax.Parser.PublicCoreTermTotalityProperties

/-! Complete ordinary grammar correspondence for raw and isolated public
Core blocks, retaining either supplied tail-expression policy. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Raw public block grammar success is exactly execution with the same AST
and declarative remainder on a valid input, under the supplied policy. -/
theorem block_ordinary_success_iff (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {value : Block} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CoreBlockPublicOrdinaryParses policy.declarative
      input.declarativeRemainder value remainder ↔
      ∃ output, block policy input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok (block policy) (block_exactOutcomeSpec policy)
    ((block_invariantFreeOnValid policy).ne_invariant input inputValid)
    (block_success_ordinary_sound policy) (block_reject_ordinary_sound policy)

/-- Raw public block grammar rejection is exactly execution at the same
declarative endpoint on a valid input, under the supplied policy. -/
theorem block_ordinary_reject_iff (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CoreBlockPublicRejects policy.declarative
      input.declarativeRemainder rejected ↔
      ∃ failure output, block policy input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject (block policy) (block_exactOutcomeSpec policy)
    ((block_invariantFreeOnValid policy).ne_invariant input inputValid)
    (block_success_ordinary_sound policy) (block_reject_ordinary_sound policy)

/-- Isolated public block grammar success is exactly capture-aware execution
with the same AST and external declarative remainder on a valid input. -/
theorem isolatedCoreBlockPublic_ordinary_success_iff
    (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {value : Block} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses policy.declarative
      input.declarativeRemainder value remainder ↔
      ∃ output, isolateBlock (block policy) input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok (isolateBlock (block policy))
    (isolatedCoreBlockPublic_exactOutcomeSpec policy)
    ((BlockInternals.isolateBlock_invariantFreeOnValid (block policy)
      (block_invariantFreeOnValid policy)).ne_invariant input inputValid)
    (isolatedCoreBlockPublic_success_ordinary_sound policy)
    (isolatedCoreBlockPublic_reject_ordinary_sound policy)

/-- Isolated public block grammar rejection is exactly execution at the same
external declarative endpoint on a valid input, under the supplied policy. -/
theorem isolatedCoreBlockPublic_ordinary_reject_iff
    (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.IsolatedCoreBlockPublicRejects policy.declarative
      input.declarativeRemainder rejected ↔
      ∃ failure output, isolateBlock (block policy) input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject (isolateBlock (block policy))
    (isolatedCoreBlockPublic_exactOutcomeSpec policy)
    ((BlockInternals.isolateBlock_invariantFreeOnValid (block policy)
      (block_invariantFreeOnValid policy)).ne_invariant input inputValid)
    (isolatedCoreBlockPublic_success_ordinary_sound policy)
    (isolatedCoreBlockPublic_reject_ordinary_sound policy)

end Solcore.Syntax.Parser
