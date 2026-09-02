import Solcore.Syntax.DeclarativeEnumConstructorOutcomeProperties
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

end Solcore.Syntax.Parser.EnumInternals
