import Solcore.Syntax.DeclarativeDelimitedTrailingOutcomeProperties
import Solcore.Syntax.DeclarativeEnumBodyOutcomeGrammar
import Solcore.Syntax.DeclarativeEnumConstructorOutcomeProperties

/-! Deterministic exact ordinary outcomes for canonical enum bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Possibly-empty, trailing-comma enum bodies have deterministic and
exclusive ordinary outcomes. -/
theorem enumBodyDeterministicOutcomeSpec :
    DeterministicOutcomeSpec EnumBodyOrdinaryOutcomeParses EnumBodyRejects := by
  have outcomes := trailingDelimitedListDeterministicOutcomeSpec
    .leftBrace .rightBrace enumConstructorDeterministicOutcomeSpec
  constructor
  · intro input left right afterLeft afterRight leftParsed rightParsed
    exact outcomes.successOutputUnique leftParsed rightParsed
  · intro input rejected rejection
    rintro ⟨body, output, parsed⟩
    exact outcomes.successRejectDisjoint rejection
      ⟨{ span := body.1, elements := body.2 }, output, parsed⟩

end Solcore.Syntax.DeclarativeGrammar
