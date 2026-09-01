import Solcore.Syntax.Parser.CanonicalParserTotalityProperties
import Solcore.Syntax.Parser.CompleteOutputProperties

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

end Solcore.Syntax.Parser
