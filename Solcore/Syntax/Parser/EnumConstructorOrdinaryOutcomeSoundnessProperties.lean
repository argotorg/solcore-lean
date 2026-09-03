import Solcore.Syntax.DeclarativeEnumConstructorExactnessProperties
import Solcore.Syntax.Parser.EnumConstructorOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.EnumConstructorOrdinarySuccessSoundnessProperties

/-! Complete executable ordinary outcomes for enum constructors and payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

/-- Package optional enum-constructor payload success and exact rejection. -/
theorem enumConstructorFields_ordinaryOutcome_sound :
    (∀ {input output : State} {fields : Option (DelimitedList TypeExpr)},
      enumConstructorFields input = .ok fields output →
        DeclarativeGrammar.OptionalEnumConstructorFieldsOrdinaryParses
          input.declarativeRemainder fields output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      enumConstructorFields input = .reject failure rejected →
        DeclarativeGrammar.OptionalEnumConstructorFieldsRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨enumConstructorFields_success_ordinaryOutcome_sound,
    enumConstructorFields_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic optional enum-constructor payload outcomes. -/
theorem enumConstructorFields_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.OptionalEnumConstructorFieldsOrdinaryParses
      DeclarativeGrammar.OptionalEnumConstructorFieldsRejects :=
  DeclarativeGrammar.optionalEnumConstructorFieldsDeterministicOutcomeSpec

/-- Package enum-constructor success and exact sequential rejection. -/
theorem enumConstructor_ordinaryOutcome_sound :
    (∀ {input output : State} {constructor : EnumConstructor},
      enumConstructor input = .ok constructor output →
        DeclarativeGrammar.EnumConstructorOrdinaryParses
          input.declarativeRemainder constructor output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      enumConstructor input = .reject failure rejected →
        DeclarativeGrammar.EnumConstructorRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨enumConstructor_success_ordinaryOutcome_sound,
    enumConstructor_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive enum-constructor outcomes. -/
theorem enumConstructor_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.EnumConstructorOrdinaryParses
      DeclarativeGrammar.EnumConstructorRejects :=
  DeclarativeGrammar.enumConstructorDeterministicOutcomeSpec

/-- Re-export exact optional enum-constructor payload outcomes. -/
theorem enumConstructorFields_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.OptionalEnumConstructorFieldsOrdinaryParses
      DeclarativeGrammar.OptionalEnumConstructorFieldsRejects :=
  DeclarativeGrammar.optionalEnumConstructorFieldsExactOutcomeSpec

/-- Two successful optional payloads fix the same value and remainder. -/
theorem enumConstructorFields_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : Option (DelimitedList TypeExpr)}
    (leftResult : enumConstructorFields input = .ok left leftOutput)
    (rightResult : enumConstructorFields input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalEnumConstructorFieldsOrdinaryParses.result_unique
    (enumConstructorFields_success_ordinaryOutcome_sound leftResult)
    (enumConstructorFields_success_ordinaryOutcome_sound rightResult)

/-- Two optional payload rejections have the same declarative endpoint. -/
theorem enumConstructorFields_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : enumConstructorFields input = .reject leftFailure leftOutput)
    (rightResult : enumConstructorFields input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalEnumConstructorFieldsRejects.output_unique
    (enumConstructorFields_reject_ordinaryOutcome_sound leftResult)
    (enumConstructorFields_reject_ordinaryOutcome_sound rightResult)

/-- Re-export unconditional exact enum-constructor outcomes. -/
theorem enumConstructor_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.EnumConstructorOrdinaryParses
      DeclarativeGrammar.EnumConstructorRejects :=
  DeclarativeGrammar.enumConstructorExactOutcomeSpec

/-- Two successful enum constructors have the same AST and remainder. -/
theorem enumConstructor_success_result_unique
    {input leftOutput rightOutput : State} {left right : EnumConstructor}
    (leftResult : enumConstructor input = .ok left leftOutput)
    (rightResult : enumConstructor input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.EnumConstructorOrdinaryParses.result_unique
    (enumConstructor_success_ordinaryOutcome_sound leftResult)
    (enumConstructor_success_ordinaryOutcome_sound rightResult)

/-- Two enum-constructor rejections have the same declarative endpoint. -/
theorem enumConstructor_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : enumConstructor input = .reject leftFailure leftOutput)
    (rightResult : enumConstructor input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.EnumConstructorRejects.output_unique
    (enumConstructor_reject_ordinaryOutcome_sound leftResult)
    (enumConstructor_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.EnumInternals
