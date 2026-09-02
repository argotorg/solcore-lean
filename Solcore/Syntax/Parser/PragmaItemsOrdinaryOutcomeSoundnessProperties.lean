import Solcore.Syntax.DeclarativePragmaItemsOutcomeProperties
import Solcore.Syntax.Parser.PragmaItemsOrdinaryRejectionSoundnessProperties

/-! Complete executable ordinary outcomes for pragma item scanning. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

/-- Package success and rejection reflection for the production tail fuel. -/
theorem pragmaItemsTail_production_ordinaryOutcome_sound
    (itemsRev : List Identifier) :
    (∀ {input output : State} {items : List Identifier},
      pragmaItemsTail (input.remainingCount + 1) itemsRev input =
          .ok items output →
        ∃ suffix,
          items = itemsRev.reverse ++ suffix ∧
          DeclarativeGrammar.PragmaItemsTailOrdinaryParses
            input.declarativeRemainder suffix output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      pragmaItemsTail (input.remainingCount + 1) itemsRev input =
          .reject failure rejected →
        DeclarativeGrammar.PragmaItemsTailRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨pragmaItemsTail_production_success_ordinaryOutcome_sound itemsRev,
    pragmaItemsTail_production_reject_ordinaryOutcome_sound itemsRev⟩

/-- Package exact executable success and rejection for public pragma items. -/
theorem pragmaItems_ordinaryOutcome_sound :
    (∀ {input output : State} {items : List Identifier},
      pragmaItems input = .ok items output →
        DeclarativeGrammar.PragmaItemsOrdinaryParses
          input.declarativeRemainder items output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      pragmaItems input = .reject failure rejected →
        DeclarativeGrammar.PragmaItemsRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨pragmaItems_success_ordinaryOutcome_sound,
    pragmaItems_reject_ordinaryOutcome_sound⟩

/-- Re-export the parser-independent deterministic pragma-tail contract. -/
theorem pragmaItemsTail_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.PragmaItemsTailOrdinaryParses
      DeclarativeGrammar.PragmaItemsTailRejects :=
  DeclarativeGrammar.pragmaItemsTailDeterministicOutcomeSpec

/-- Re-export the parser-independent deterministic pragma-item contract. -/
theorem pragmaItems_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.PragmaItemsOrdinaryParses
      DeclarativeGrammar.PragmaItemsRejects :=
  DeclarativeGrammar.pragmaItemsDeterministicOutcomeSpec

end Solcore.Syntax.Parser.PragmaInternals
