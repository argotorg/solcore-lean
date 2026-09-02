import Solcore.Syntax.DeclarativeTraitBodyExactnessProperties
import Solcore.Syntax.Parser.TraitBodyOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.TraitBodyOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for trait bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TraitInternals

/-- Package executable trait-body success and exact rejection. -/
theorem traitBody_ordinaryOutcome_sound :
    (∀ {input output : State} {body : TraitBody},
      traitBody input = .ok body output →
        DeclarativeGrammar.TraitBodyOrdinaryOutcomeParses
          input.declarativeRemainder (body.span, body.methods)
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      traitBody input = .reject failure rejected →
        DeclarativeGrammar.TraitBodyRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨traitBody_success_ordinaryOutcome_sound,
    traitBody_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad trait-body outcomes. -/
theorem traitBody_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TraitBodyOrdinaryOutcomeParses
      DeclarativeGrammar.TraitBodyRejects :=
  DeclarativeGrammar.traitBodyDeterministicOutcomeSpec

/-- Re-export unconditional exact trait-body outcomes. -/
theorem traitBody_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TraitBodyOrdinaryOutcomeParses
      DeclarativeGrammar.TraitBodyRejects :=
  DeclarativeGrammar.traitBodyExactOutcomeSpec

/-- Two successful trait bodies have the same span, methods, and declarative
remainder. -/
theorem traitBody_success_result_unique
    {input leftOutput rightOutput : State} {left right : TraitBody}
    (leftResult : traitBody input = .ok left leftOutput)
    (rightResult : traitBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder := by
  rcases traitBody_exactOutcomeSpec.successResultUnique
      (traitBody_success_ordinaryOutcome_sound leftResult)
      (traitBody_success_ordinaryOutcome_sound rightResult) with
    ⟨bodyEq, outputEq⟩
  constructor
  · cases left
    cases right
    cases bodyEq
    rfl
  · exact outputEq

/-- Two trait-body rejections have the same declarative endpoint. -/
theorem traitBody_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : traitBody input = .reject leftFailure leftOutput)
    (rightResult : traitBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TraitBodyRejects.output_unique
    (traitBody_reject_ordinaryOutcome_sound leftResult)
    (traitBody_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.TraitInternals
