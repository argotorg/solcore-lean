import Solcore.Syntax.DeclarativePlainTopItemOutcomeProperties
import Solcore.Syntax.Parser.PlainTopItemOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.PlainTopItemOrdinarySuccessSoundnessProperties

/-! Complete broad executable outcomes for plain top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Package unconditional executable success and exact selected-branch
rejection for attribute-free top items. -/
theorem plainTopItem_ordinaryOutcome_sound :
    (∀ {input output : State} {item : TopItem},
      plainTopItem input = .ok item output →
        DeclarativeGrammar.PlainTopItemOrdinaryParses
          input.declarativeRemainder item output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      plainTopItem input = .reject failure rejected →
        DeclarativeGrammar.PlainTopItemRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨plainTopItem_success_ordinaryOutcome_sound,
    plainTopItem_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad plain-top-item outcomes. -/
theorem plainTopItem_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.PlainTopItemOrdinaryParses
      DeclarativeGrammar.PlainTopItemRejects :=
  DeclarativeGrammar.plainTopItemDeterministicOutcomeSpec

end Solcore.Syntax.Parser.FileInternals
