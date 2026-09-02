import Solcore.Syntax.DeclarativeNamespaceImportOutcomeProperties
import Solcore.Syntax.Parser.NamespaceImportOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.NamespaceImportOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for namespace import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package namespace-import success and exact stagewise rejection. -/
theorem namespaceImport_ordinaryOutcome_sound (start : SourceSpan) :
    (∀ {input output : State} {declaration : ImportDecl},
      ImportInternals.namespaceImport start input = .ok declaration output →
        DeclarativeGrammar.NamespaceImportOrdinaryParses start
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.namespaceImport start input = .reject failure rejected →
        DeclarativeGrammar.NamespaceImportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨namespaceImport_success_ordinaryOutcome_sound start,
    namespaceImport_reject_ordinaryOutcome_sound start⟩

/-- Re-export deterministic and exclusive namespace-import outcomes. -/
theorem namespaceImport_ordinaryOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.NamespaceImportOrdinaryParses start)
      DeclarativeGrammar.NamespaceImportRejects :=
  DeclarativeGrammar.namespaceImportDeterministicOutcomeSpec start

end Solcore.Syntax.Parser
