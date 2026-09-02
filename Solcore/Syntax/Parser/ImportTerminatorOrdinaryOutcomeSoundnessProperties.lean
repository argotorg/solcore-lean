import Solcore.Syntax.DeclarativeImportTerminatorOutcomeProperties
import Solcore.Syntax.Parser.ImportTerminatorOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ImportTerminatorOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for import terminators. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package import-terminator semicolon/recovery success and exact rejection. -/
theorem importTerminator_ordinaryOutcome_sound (lastSpan : SourceSpan) :
    (∀ {input output : State} {endSpan : SourceSpan},
      ImportInternals.terminator lastSpan input = .ok endSpan output →
        DeclarativeGrammar.ImportTerminatorOrdinaryParses lastSpan
          input.declarativeRemainder endSpan output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.terminator lastSpan input = .reject failure rejected →
        DeclarativeGrammar.ImportTerminatorRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨importTerminator_success_ordinaryOutcome_sound lastSpan,
    importTerminator_reject_ordinaryOutcome_sound lastSpan⟩

/-- Re-export deterministic and exclusive import-terminator outcomes. -/
theorem importTerminator_ordinaryOutcomeSpec (lastSpan : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ImportTerminatorOrdinaryParses lastSpan)
      DeclarativeGrammar.ImportTerminatorRejects :=
  DeclarativeGrammar.importTerminatorDeterministicOutcomeSpec lastSpan

end Solcore.Syntax.Parser
