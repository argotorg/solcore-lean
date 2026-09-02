import Solcore.Syntax.DeclarativeWildcardImportOutcomeProperties
import Solcore.Syntax.Parser.WildcardImportOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.WildcardImportOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for wildcard import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package wildcard-import success and exact stagewise rejection. -/
theorem wildcardImport_ordinaryOutcome_sound (start : SourceSpan) :
    (∀ {input output : State} {declaration : ImportDecl},
      ImportInternals.wildcardImport start input = .ok declaration output →
        DeclarativeGrammar.WildcardImportOrdinaryParses start
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.wildcardImport start input = .reject failure rejected →
        DeclarativeGrammar.WildcardImportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨wildcardImport_success_ordinaryOutcome_sound start,
    wildcardImport_reject_ordinaryOutcome_sound start⟩

/-- Re-export deterministic and exclusive wildcard-import outcomes. -/
theorem wildcardImport_ordinaryOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.WildcardImportOrdinaryParses start)
      DeclarativeGrammar.WildcardImportRejects :=
  DeclarativeGrammar.wildcardImportDeterministicOutcomeSpec start

end Solcore.Syntax.Parser
