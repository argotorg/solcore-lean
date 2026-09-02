import Solcore.Syntax.DeclarativeTopItemOutcomeProperties
import Solcore.Syntax.Parser.TopItemOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.TopItemOrdinarySuccessSoundnessProperties

/-! Complete broad executable outcomes for derive-aware top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Package unconditional executable success and exact selected-stage
rejection for complete derive-aware top items. -/
theorem topItem_ordinaryOutcome_sound :
    (∀ {input output : State} {item : TopItem},
      topItem input = .ok item output →
        DeclarativeGrammar.TopItemOrdinaryParses
          input.declarativeRemainder item output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      topItem input = .reject failure rejected →
        DeclarativeGrammar.TopItemRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨topItem_success_ordinaryOutcome_sound,
    topItem_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive derive-aware top-item outcomes. -/
theorem topItem_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses
      DeclarativeGrammar.TopItemRejects :=
  DeclarativeGrammar.topItemDeterministicOutcomeSpec

end Solcore.Syntax.Parser.FileInternals
