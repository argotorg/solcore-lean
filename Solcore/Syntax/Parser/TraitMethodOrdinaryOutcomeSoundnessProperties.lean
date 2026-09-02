import Solcore.Syntax.DeclarativeTraitMethodExactnessProperties
import Solcore.Syntax.Parser.TraitMethodOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.TraitMethodOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for trait methods. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TraitInternals

/-- Package executable trait-method success and exact rejection. -/
theorem traitMethod_ordinaryOutcome_sound :
    (∀ {input output : State} {method : TraitMethod},
      traitMethod input = .ok method output →
        DeclarativeGrammar.TraitMethodOrdinaryParses
          input.declarativeRemainder method output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      traitMethod input = .reject failure rejected →
        DeclarativeGrammar.TraitMethodRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨traitMethod_success_ordinaryOutcome_sound,
    traitMethod_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad trait-method outcomes. -/
theorem traitMethod_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TraitMethodOrdinaryParses
      DeclarativeGrammar.TraitMethodRejects :=
  DeclarativeGrammar.traitMethodDeterministicOutcomeSpec

/-- Re-export unconditional exact trait-method outcomes. -/
theorem traitMethod_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TraitMethodOrdinaryParses
      DeclarativeGrammar.TraitMethodRejects :=
  DeclarativeGrammar.traitMethodExactOutcomeSpec

/-- Two successful trait methods have the same AST and declarative remainder. -/
theorem traitMethod_success_result_unique
    {input leftOutput rightOutput : State} {left right : TraitMethod}
    (leftResult : traitMethod input = .ok left leftOutput)
    (rightResult : traitMethod input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TraitMethodOrdinaryParses.result_unique
    (traitMethod_success_ordinaryOutcome_sound leftResult)
    (traitMethod_success_ordinaryOutcome_sound rightResult)

/-- Two trait-method rejections have the same declarative endpoint. -/
theorem traitMethod_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : traitMethod input = .reject leftFailure leftOutput)
    (rightResult : traitMethod input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TraitMethodRejects.output_unique
    (traitMethod_reject_ordinaryOutcome_sound leftResult)
    (traitMethod_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.TraitInternals
