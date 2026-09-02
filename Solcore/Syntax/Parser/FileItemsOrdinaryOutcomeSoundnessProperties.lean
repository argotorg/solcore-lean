import Solcore.Syntax.DeclarativeFileItemsOutcomeProperties
import Solcore.Syntax.Parser.FileItemsOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.FileItemsOrdinarySuccessSoundnessProperties

/-! Complete broad executable outcomes for source-file item accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Package exact executable success and rejection for any fuel and reverse
accumulator, keeping the latter outside the declarative grammar. -/
theorem parseItems_ordinaryOutcome_sound (fuel : Nat)
    (itemsRev : List TopItem) :
    (∀ {input output : State} {items : List TopItem},
      parseItems fuel itemsRev input = .ok items output →
        ∃ suffix,
          items = itemsRev.reverse ++ suffix ∧
          DeclarativeGrammar.FileItemsOrdinaryParses
            input.declarativeRemainder suffix output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      parseItems fuel itemsRev input = .reject failure rejected →
        DeclarativeGrammar.FileItemsRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨fun {input output items} result =>
      parseItems_success_ordinaryOutcome_sound_strong fuel itemsRev input
        items output result,
    fun {input rejected failure} result =>
      parseItems_reject_ordinaryOutcome_sound fuel itemsRev input failure
        rejected result⟩

/-- Re-export deterministic and exclusive broad file-item outcomes. -/
theorem parseItems_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.FileItemsOrdinaryParses
      DeclarativeGrammar.FileItemsRejects :=
  DeclarativeGrammar.fileItemsDeterministicOutcomeSpec

end Solcore.Syntax.Parser.FileInternals
