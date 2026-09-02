import Solcore.Syntax.DeclarativeSelectiveImportOutcomeProperties
import Solcore.Syntax.Parser.SelectiveImportOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.SelectiveImportOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for selective import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package selective-import success and exact stagewise rejection. -/
theorem selectiveImport_ordinaryOutcome_sound (start : SourceSpan) :
    (∀ {input output : State} {declaration : ImportDecl},
      ImportInternals.selectiveImport start input = .ok declaration output →
        DeclarativeGrammar.SelectiveImportOrdinaryParses start
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.selectiveImport start input = .reject failure rejected →
        DeclarativeGrammar.SelectiveImportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨selectiveImport_success_ordinaryOutcome_sound start,
    selectiveImport_reject_ordinaryOutcome_sound start⟩

/-- Re-export deterministic and exclusive selective-import outcomes. -/
theorem selectiveImport_ordinaryOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.SelectiveImportOrdinaryParses start)
      DeclarativeGrammar.SelectiveImportRejects :=
  DeclarativeGrammar.selectiveImportDeterministicOutcomeSpec start

end Solcore.Syntax.Parser
