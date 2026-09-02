import Solcore.Syntax.Parser.CanonicalParserTotalityProperties
import Solcore.Syntax.Parser.CompleteOutputProperties
import Solcore.Syntax.Parser.PublicSourceFileOrdinaryOutcomeSoundnessProperties

/-! Total public parsing with complete provenance for the returned output. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Valid tokenized input produces an output whose complete provenance belongs
to the source file. -/
theorem productionParseLexed_exists_ok_completeOutput_validFor
    (file : SourceFile) (lexed : LexedFile) (lexedValid : lexed.ValidFor file) :
    ∃ output,
      parseLexed file lexed = .ok output ∧ output.CanonicalValidFor file := by
  rcases productionParseLexed_exists_ok file lexed lexedValid with
    ⟨output, parsed⟩
  exact ⟨output, parsed,
    parseLexed_ok_completeOutput_validFor file lexed output parsed⟩

/-- Every source file produces an output whose complete provenance belongs to
that source file. -/
theorem productionParse_exists_ok_completeOutput_validFor
    (file : SourceFile) :
    ∃ output, parse file = .ok output ∧ output.CanonicalValidFor file := by
  rcases productionParse_exists_ok file with ⟨output, parsed⟩
  exact ⟨output, parsed, parse_ok_completeOutput_validFor file output parsed⟩

/-- Valid tokenized input produces a broad public syntax derivation together
with the complete canonical output contract. -/
theorem productionParseLexed_exists_ok_publicSourceFileOrdinary
    (file : SourceFile) (lexed : LexedFile) (lexedValid : lexed.ValidFor file) :
    ∃ output,
      parseLexed file lexed = .ok output ∧
        DeclarativeGrammar.PublicSourceFileOrdinaryParses file
          lexed.tokens lexed.comments output.parsed ∧
        output.CanonicalValidFor file := by
  rcases productionParseLexed_exists_ok file lexed lexedValid with
    ⟨output, parsed⟩
  exact ⟨output, parsed,
    parseLexed_ok_publicSourceFileOrdinary_sound_and_validFor parsed⟩

/-- Every source file produces a broad public syntax derivation over its exact
retained carriers together with the complete canonical output contract. -/
theorem productionParse_exists_ok_publicSourceFileOrdinary
    (file : SourceFile) :
    ∃ output,
      parse file = .ok output ∧
        DeclarativeGrammar.PublicSourceFileOrdinaryParses file
          output.tokens output.parsed.comments output.parsed ∧
        output.CanonicalValidFor file := by
  rcases productionParse_exists_ok file with ⟨output, parsed⟩
  exact ⟨output, parsed,
    parse_ok_publicSourceFileOrdinary_sound_and_validFor parsed⟩

end Solcore.Syntax.Parser
