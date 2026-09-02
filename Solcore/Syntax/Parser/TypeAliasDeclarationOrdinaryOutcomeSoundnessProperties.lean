import Solcore.Syntax.DeclarativeTypeAliasOutcomeProperties
import Solcore.Syntax.Parser.TypeAliasDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.TypeAliasDeclarationOrdinarySuccessSoundnessProperties

/-! Complete executable ordinary outcomes for transparent type aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package exact executable type-alias success and rejection. -/
theorem typeAlias_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : TypeAliasDecl},
      typeAlias input = .ok declaration output →
        DeclarativeGrammar.TypeAliasDeclOrdinaryParses
          input.declarativeRemainder declaration
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      typeAlias input = .reject failure rejected →
        DeclarativeGrammar.TypeAliasDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨typeAlias_success_ordinaryOutcome_sound,
    typeAlias_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic broad type-alias outcomes. -/
theorem typeAlias_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TypeAliasDeclOrdinaryParses
      DeclarativeGrammar.TypeAliasDeclRejects :=
  DeclarativeGrammar.typeAliasDeclDeterministicOutcomeSpec

end Solcore.Syntax.Parser
