import Solcore.Syntax.DeclarativeEnumBodyExactnessProperties
import Solcore.Syntax.Parser.EnumBodyOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.EnumBodyOrdinarySuccessSoundnessProperties

/-! Complete executable ordinary outcomes for canonical enum bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

/-- Package executable enum-body success and exact rejection. -/
theorem enumBody_ordinaryOutcome_sound :
    (∀ {input output : State} {body : EnumBody},
      enumBody input = .ok body output →
        DeclarativeGrammar.EnumBodyOrdinaryOutcomeParses
          input.declarativeRemainder (body.span, body.constructors)
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      enumBody input = .reject failure rejected →
        DeclarativeGrammar.EnumBodyRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨enumBody_success_ordinaryOutcome_sound,
    enumBody_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive enum-body ordinary outcomes. -/
theorem enumBody_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.EnumBodyOrdinaryOutcomeParses
      DeclarativeGrammar.EnumBodyRejects :=
  DeclarativeGrammar.enumBodyDeterministicOutcomeSpec

/-- Re-export unconditional exact enum-body outcomes. -/
theorem enumBody_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.EnumBodyOrdinaryOutcomeParses
      DeclarativeGrammar.EnumBodyRejects :=
  DeclarativeGrammar.enumBodyExactOutcomeSpec

/-- Two successful enum bodies have the same span, constructors, and remainder. -/
theorem enumBody_success_result_unique
    {input leftOutput rightOutput : State} {left right : EnumBody}
    (leftResult : enumBody input = .ok left leftOutput)
    (rightResult : enumBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder := by
  rcases enumBody_exactOutcomeSpec.successResultUnique
      (enumBody_success_ordinaryOutcome_sound leftResult)
      (enumBody_success_ordinaryOutcome_sound rightResult) with
    ⟨bodyEq, outputEq⟩
  constructor
  · cases left
    cases right
    cases bodyEq
    rfl
  · exact outputEq

/-- Two enum-body rejections have the same declarative endpoint. -/
theorem enumBody_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : enumBody input = .reject leftFailure leftOutput)
    (rightResult : enumBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.EnumBodyRejects.output_unique
    (enumBody_reject_ordinaryOutcome_sound leftResult)
    (enumBody_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.EnumInternals
