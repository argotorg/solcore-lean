import Solcore.Syntax.DeclarativePlainImportOutcomeProperties
import Solcore.Syntax.Parser.PlainImportOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.PlainImportOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for plain import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package plain-import success and exact path/terminator rejection. -/
theorem plainImport_ordinaryOutcome_sound (start : SourceSpan) :
    (∀ {input output : State} {declaration : ImportDecl},
      ImportInternals.plainImport start input = .ok declaration output →
        DeclarativeGrammar.PlainImportOrdinaryParses start
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.plainImport start input = .reject failure rejected →
        DeclarativeGrammar.PlainImportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨plainImport_success_ordinaryOutcome_sound start,
    plainImport_reject_ordinaryOutcome_sound start⟩

/-- Re-export deterministic and exclusive plain-import outcomes. -/
theorem plainImport_ordinaryOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.PlainImportOrdinaryParses start)
      DeclarativeGrammar.PlainImportRejects :=
  DeclarativeGrammar.plainImportDeterministicOutcomeSpec start

end Solcore.Syntax.Parser
